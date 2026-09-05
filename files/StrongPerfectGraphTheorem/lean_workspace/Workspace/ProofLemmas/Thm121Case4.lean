import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.Statements.S10.Thm_10_4
import Workspace.Statements.S11.Thm_11_2
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.PrismFromBanisterAndStep
import Workspace.ProofLemmas.Thm121C3PathCons
import Workspace.ProofLemmas.Thm121MinorCriteria
import Workspace.ProofLemmas.Thm121Symmetry

/-!
# 12.1, case (4) of the printed proof

PAPER (printed pp. 69–70): *"(4) If `v` is nonadjacent to both `a₀, b₀` then the theorem holds.*

*For then we may assume that `v` has a neighbour in `V(S)`, since otherwise it is minor, and
statement 3 of the theorem holds.  Suppose first that `v` also has a neighbour in `R₀*`.  If `v`
is a left-star then statement 3 holds, so we assume not; and then by 11.2, `v` is `B`-complete.
Similarly `v` is `A`-complete and therefore central, and statement 2 holds.  Thus we may assume
that `v` has no neighbour in `V(R₀)`, and therefore `v` is minor.  We claim that statement 1
holds, and to show this we may assume that `v` is `A`-complete.  Let `a₁`-`R₁`-`b₁`,
`a₂`-`R₂`-`b₂` be a step; then by 10.4, `v` has no neighbour in `R₁ \ a₁` or in `R₂ \ a₂`, and
therefore `v` is a left-star, and statement 1 holds.  This proves (4)."*

Map of the printed argument onto this file:

* *"we may assume that `v` has a neighbour in `V(S)`, since otherwise it is minor"* — the outer
  `by_cases hVS`, closed by `Thm121MinorCriteria.thm121AltOneOfNoStripNeighbour`.  (The printed
  *"statement 3"* is the recorded erratum for *"statement 1"*.)
* *"Suppose first that `v` also has a neighbour in `R₀*`"* — the inner `by_cases hR0`.  Since
  `v` is nonadjacent to both ends of `R₀`, a neighbour on `R₀` is automatically in `R₀*`.
* *"If `v` is a left-star then statement 3 holds … by 11.2, `v` is `B`-complete.  Similarly `v`
  is `A`-complete"* — `case4Link` below, which builds the two paths 11.2 asks for and applies
  11.2 twice: once to `(A, C, B)` with the banister `a₀`-`R₀`-`b₀`, and once to the reflected
  staircase `(B, C, A)` with `b₀`-`R₀ᵣ`-`a₀` (the paper's *"similarly"*, formalized in
  `Thm121Symmetry.thm121SwapStaircase`).  The two paths are the same two paths in both calls,
  with their rôles exchanged.
* *"and therefore central, and statement 2 holds"* — `CentralForStaircase` and
  `MajorForStaircase` are read off from the two completeness facts.
* *"Let `a₁`-`R₁`-`b₁`, `a₂`-`R₂`-`b₂` be a step; then by 10.4 …"* —
  `leftStar_of_ACompleteMinor` below.  The step is the one supplied by step-connectedness
  through the putative neighbour `w ∈ B ∪ C`; the prism 10.4 is applied to is the one formed by
  that step together with the banister as third rung
  (`PrismFromBanisterAndStep.formPrism_of_banister_and_step`), and `F = {v}`, whose
  `F.Nontrivial` conclusion is the contradiction.
* the mirror half *"(right-star ∨ ¬ `B`-complete)"* of statement 1 is the same lemma applied
  through `Thm121Symmetry.thm121SwapStaircase`, which is the paper's *"up to symmetry"*.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm121Case4

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

/-! ### List/index bookkeeping -/

/-- Two `getElem`s at provably equal indices agree. -/
private theorem getElem_eq_of_eq {V : Type*} {l : List V} {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) (h : i = j) : l[i]'hi = l[j]'hj := by
  subst h; rfl

/-- The neighbour of `v` on `l` furthest along `l`. -/
private theorem exists_max_adj {V : Type*} (G : SimpleGraph V) (v : V) (l : List V)
    (k0 : ℕ) (hk0 : k0 < l.length) (hk0adj : G.Adj v (l[k0]'hk0)) :
    ∃ (i : ℕ) (hilt : i < l.length), G.Adj v (l[i]'hilt) ∧
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
  refine ⟨T.max' hne, hlt, hadj, ?_⟩
  intro m hm hgt hadjm
  have hle : m ≤ T.max' hne := Finset.le_max' T m ((hmemT m).mpr ⟨hm, hm, hadjm⟩)
  omega

/-- The neighbour of `v` on `l` closest to the front of `l`. -/
private theorem exists_min_adj {V : Type*} (G : SimpleGraph V) (v : V) (l : List V)
    (k0 : ℕ) (hk0 : k0 < l.length) (hk0adj : G.Adj v (l[k0]'hk0)) :
    ∃ (i : ℕ) (hilt : i < l.length), G.Adj v (l[i]'hilt) ∧
      ∀ (m : ℕ) (hm : m < l.length), m < i → ¬ G.Adj v (l[m]'hm) := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = (Finset.range l.length).filter
      (fun k => ∃ h : k < l.length, G.Adj v (l[k]'h)) := ⟨_, rfl⟩
  have hmemT : ∀ k : ℕ,
      k ∈ T ↔ (k < l.length ∧ ∃ h : k < l.length, G.Adj v (l[k]'h)) := by
    intro k
    rw [hT, Finset.mem_filter, Finset.mem_range]
  have hne : T.Nonempty := ⟨k0, (hmemT k0).mpr ⟨hk0, hk0, hk0adj⟩⟩
  obtain ⟨hlt, _, hadj⟩ := (hmemT _).mp (Finset.min'_mem T hne)
  refine ⟨T.min' hne, hlt, hadj, ?_⟩
  intro m hm hgt hadjm
  have hle : T.min' hne ≤ m := Finset.min'_le T m ((hmemT m).mpr ⟨hm, hm, hadjm⟩)
  omega

/-- Every vertex of a rung of `S = (A, C, B)` lies in `V(S)`. -/
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

/-- Exchanging the two rungs of a step. -/
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

/-! ### The application of 11.2, in both orientations

PAPER: *"If `v` is a left-star then statement 3 holds, so we assume not; and then by 11.2, `v`
is `B`-complete.  Similarly `v` is `A`-complete."*

Both applications of 11.2 use the same two paths: `P` runs from `v` back along `R₀` to `a₀`
through the neighbour of `v` on `R₀` closest to `a₀`, and `Q` runs from `v` along `R₀` to `b₀`
through the neighbour closest to `b₀`.  For the reflected staircase `(B, C, A)`,
`b₀`-`R₀ᵣ`-`a₀`, the two paths simply exchange rôles. -/
private theorem case4Link {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    (v : V) (hv : v ∉ staircaseVertices A C B R₀)
    (hvS : ∃ x ∈ A ∪ B ∪ C, G.Adj v x)
    (ha : ¬ G.Adj v a₀) (hb : ¬ G.Adj v b₀)
    (hintN : ∃ x ∈ SPGT.interior R₀, G.Adj v x) :
    (SPGT.VertexComplete G v B ∨ IsLeftStar G A C B v) ∧
      (SPGT.VertexComplete G v A ∨ IsLeftStar G B C A v) := by
  classical
  have hS : StepConnected G A C B := hK.1.1
  have hban : IsBanister G A C B a₀ R₀ b₀ := hK.1.2.1
  have hlen0 : 3 ≤ SPGT.pathLength R₀ := hK.1.2.2
  obtain ⟨hR0, hR0S, hlstar, hrstar, hantiint⟩ := id hban
  have hlp : SPGT.pathLength R₀ = R₀.length - 1 := rfl
  rw [hlp] at hlen0
  have hlen4 : 4 ≤ R₀.length := by omega
  have hjlt : R₀.length - 1 < R₀.length := by omega
  have hzlt : 0 < R₀.length := by omega
  have ha0 : R₀[0]'hzlt = a₀ := PathBasics.getElem_zero_of_head? hR0.2.1 hzlt
  have hb0 : R₀[R₀.length - 1]'hjlt = b₀ :=
    PathBasics.getElem_last_of_getLast? hR0.2.2 (by omega)
  have ha0mem : a₀ ∈ R₀ := PathBasics.head_mem hR0.2.1
  have hb0mem : b₀ ∈ R₀ := PathBasics.getLast_mem hR0.2.2
  have hvABC : v ∉ A ∪ B ∪ C := fun h => hv (Set.mem_union_right _ h)
  have hvR0 : v ∉ R₀ := fun h => hv (Set.mem_union_left _ h)
  obtain ⟨x, hxint, hvx⟩ := hintN
  obtain ⟨k0, hk0, hk01, hk02, hk0x⟩ := PathBasics.exists_getElem_of_mem_interior hR0.1 hxint
  have hk0adj : G.Adj v (R₀[k0]'hk0) := by rw [hk0x]; exact hvx
  obtain ⟨i, hilt, hiadj, hmax⟩ := exists_max_adj G v R₀ k0 hk0 hk0adj
  obtain ⟨j, hjltn, hjadj, hmin⟩ := exists_min_adj G v R₀ k0 hk0 hk0adj
  -- both extreme neighbours are internal vertices of `R₀`
  have hi1 : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with rfl | h
    · refine absurd ?_ ha
      have hz : R₀[0]'hilt = a₀ := ha0
      rw [← hz]; exact hiadj
    · exact h
  have hi2 : i + 2 ≤ R₀.length := by
    by_contra hcon
    refine hb ?_
    have hii : (R₀[i]'hilt) = b₀ := by
      rw [getElem_eq_of_eq hilt hjlt (show i = R₀.length - 1 by omega)]; exact hb0
    rw [← hii]; exact hiadj
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · refine absurd ?_ ha
      have hz : R₀[0]'hjltn = a₀ := ha0
      rw [← hz]; exact hjadj
    · exact h
  have hj2 : j + 2 ≤ R₀.length := by
    by_contra hcon
    refine hb ?_
    have hjj : (R₀[j]'hjltn) = b₀ := by
      rw [getElem_eq_of_eq hjltn hjlt (show j = R₀.length - 1 by omega)]; exact hb0
    rw [← hjj]; exact hjadj
  have hij : i < R₀.length - 1 := by omega
  have hj0 : 0 < j := hj1
  -- `Q`: from `v` along `R₀` to `b₀`
  have hvQ0 : v ∉ (R₀.drop i).take (R₀.length - 1 - i + 1) := fun hh =>
    hvR0 (List.mem_of_mem_drop (List.mem_of_mem_take hh))
  have hadjQ0 : ∀ y ∈ (R₀.drop i).take (R₀.length - 1 - i + 1),
      (G.Adj v y ↔ y = R₀[i]'hilt) := by
    intro y hy
    obtain ⟨k, hk, hk1, hk2, hky⟩ :=
      (PathBasics.mem_slice_iff R₀ (le_of_lt hij) hjlt).mp hy
    constructor
    · intro hadj
      have hkeq : k = i := by
        by_contra hnee
        exact hmax k hk (by omega) (by rw [hky]; exact hadj)
      rw [← hky, getElem_eq_of_eq hk hilt hkeq]
    · intro hyi
      rw [hyi]; exact hiadj
  have hQ : IsPathFrom G (v :: (R₀.drop i).take (R₀.length - 1 - i + 1)) v b₀ := by
    have hslice := PathBasics.isPathFrom_slice hR0.1 hij hjlt
    have hcons := Thm121C3PathCons.isPathFrom_cons hslice hvQ0 hadjQ0
    rw [hb0] at hcons
    exact hcons
  -- `P`: from `v` back along `R₀` to `a₀`
  have hvP0 : v ∉ ((R₀.drop 0).take (j - 0 + 1)).reverse := fun hh =>
    hvR0 (List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_reverse.mp hh)))
  have hadjP0 : ∀ y ∈ ((R₀.drop 0).take (j - 0 + 1)).reverse,
      (G.Adj v y ↔ y = R₀[j]'hjltn) := by
    intro y hy
    obtain ⟨k, hk, hk1, hk2, hky⟩ :=
      (PathBasics.mem_slice_iff R₀ (Nat.zero_le j) hjltn).mp (List.mem_reverse.mp hy)
    constructor
    · intro hadj
      have hkeq : k = j := by
        by_contra hnee
        exact hmin k hk (by omega) (by rw [hky]; exact hadj)
      rw [← hky, getElem_eq_of_eq hk hjltn hkeq]
    · intro hyj
      rw [hyj]; exact hjadj
  have hP : IsPathFrom G (v :: ((R₀.drop 0).take (j - 0 + 1)).reverse) v a₀ := by
    have hslice := PathBasics.isPathFrom_slice hR0.1 hj0 hjltn
    have hrev := PathBasics.isPathFrom_reverse hslice
    have hcons := Thm121C3PathCons.isPathFrom_cons hrev hvP0 hadjP0
    rw [ha0] at hcons
    exact hcons
  -- the two "avoidance" conditions
  have hmemQ : ∀ w ∈ (R₀.drop i).take (R₀.length - 1 - i + 1),
      ∃ (k : ℕ) (hk : k < R₀.length), i ≤ k ∧ k ≤ R₀.length - 1 ∧ (R₀[k]'hk) = w :=
    fun w hw => (PathBasics.mem_slice_iff R₀ (le_of_lt hij) hjlt).mp hw
  have hmemP : ∀ w ∈ ((R₀.drop 0).take (j - 0 + 1)).reverse,
      ∃ (k : ℕ) (hk : k < R₀.length), 0 ≤ k ∧ k ≤ j ∧ (R₀[k]'hk) = w :=
    fun w hw => (PathBasics.mem_slice_iff R₀ (Nat.zero_le j) hjltn).mp (List.mem_reverse.mp hw)
  have hQavoid : ∀ w ∈ v :: (R₀.drop i).take (R₀.length - 1 - i + 1),
      w ∉ (A ∪ B ∪ C) ∪ ({a₀} : Set V) := by
    intro w hw hcon
    rcases List.mem_cons.mp hw with rfl | hwQ
    · rcases hcon with h | h
      · exact hvABC h
      · exact hvR0 (by rw [(h : w = a₀)]; exact ha0mem)
    · have hwR : w ∈ R₀ := List.mem_of_mem_drop (List.mem_of_mem_take hwQ)
      rcases hcon with h | h
      · exact hR0S w hwR h
      · obtain ⟨k, hk, hk1, hk2, hkw⟩ := hmemQ w hwQ
        have hne0 : (R₀[k]'hk) ≠ (R₀[0]'hzlt) :=
          PathBasics.path_ne_of_ne_index hR0.1 hk hzlt (by omega)
        exact hne0 (by rw [hkw, (h : w = a₀), ← ha0])
  have hPavoid : ∀ w ∈ v :: ((R₀.drop 0).take (j - 0 + 1)).reverse,
      w ∉ (A ∪ B ∪ C) ∪ ({b₀} : Set V) := by
    intro w hw hcon
    rcases List.mem_cons.mp hw with rfl | hwP
    · rcases hcon with h | h
      · exact hvABC h
      · exact hvR0 (by rw [(h : w = b₀)]; exact hb0mem)
    · have hwR : w ∈ R₀ :=
        List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_reverse.mp hwP))
      rcases hcon with h | h
      · exact hR0S w hwR h
      · obtain ⟨k, hk, hk1, hk2, hkw⟩ := hmemP w hwP
        have hne0 : (R₀[k]'hk) ≠ (R₀[R₀.length - 1]'hjlt) :=
          PathBasics.path_ne_of_ne_index hR0.1 hk hjlt (by omega)
        exact hne0 (by rw [hkw, (h : w = b₀), ← hb0])
  -- the interiors of both paths lie in `R₀*`, which is anticomplete to `V(S)`
  have hPQint : SPGT.Anticomplete G
      ({w : V | w ∈ SPGT.interior (v :: ((R₀.drop 0).take (j - 0 + 1)).reverse)} ∪
        {w : V | w ∈ SPGT.interior (v :: (R₀.drop i).take (R₀.length - 1 - i + 1))})
      (A ∪ B ∪ C) := by
    rintro w (hw | hw)
    · obtain ⟨hwmem, hwv, hwa⟩ := (PathBasics.mem_interior_iff_of_pathFrom hP).mp hw
      have hwP : w ∈ ((R₀.drop 0).take (j - 0 + 1)).reverse := by
        rcases List.mem_cons.mp hwmem with h | h
        · exact absurd h hwv
        · exact h
      obtain ⟨k, hk, hk1, hk2, hkw⟩ := hmemP w hwP
      have hkne : k ≠ 0 := by
        intro hcon
        exact hwa (by rw [← hkw, getElem_eq_of_eq hk hzlt hcon]; exact ha0)
      have hwint : w ∈ SPGT.interior R₀ := by
        rw [← hkw]
        exact PathBasics.getElem_mem_interior hR0.1 hk (by omega) (by omega)
      exact hantiint w hwint
    · obtain ⟨hwmem, hwv, hwb⟩ := (PathBasics.mem_interior_iff_of_pathFrom hQ).mp hw
      have hwQ : w ∈ (R₀.drop i).take (R₀.length - 1 - i + 1) := by
        rcases List.mem_cons.mp hwmem with h | h
        · exact absurd h hwv
        · exact h
      obtain ⟨k, hk, hk1, hk2, hkw⟩ := hmemQ w hwQ
      have hkne : k ≠ R₀.length - 1 := by
        intro hcon
        exact hwb (by rw [← hkw, getElem_eq_of_eq hk hjlt hcon]; exact hb0)
      have hwint : w ∈ SPGT.interior R₀ := by
        rw [← hkw]
        exact PathBasics.getElem_mem_interior hR0.1 hk (by omega) (by omega)
      exact hantiint w hwint
  -- 11.2, first orientation
  have hfirst : SPGT.VertexComplete G v B ∨ IsLeftStar G A C B v :=
    _root_.Workspace.Statements.S11.SPGT.thm_11_2 G hG hK4 A C B hS a₀ b₀ R₀ hban v hvABC hvS hb
      (v :: ((R₀.drop 0).take (j - 0 + 1)).reverse)
      (v :: (R₀.drop i).take (R₀.length - 1 - i + 1)) hP hPavoid hQ hQavoid hPQint
  -- 11.2, reflected orientation — the paper's "similarly"
  have hswap : MaximalStaircase G B C A b₀ R₀.reverse a₀ :=
    Thm121Symmetry.thm121SwapStaircase G A C B a₀ b₀ R₀ hK
  have hUC : B ∪ A ∪ C = A ∪ B ∪ C := by rw [Set.union_comm B A]
  have hvABC' : v ∉ B ∪ A ∪ C := by rw [hUC]; exact hvABC
  have hvS' : ∃ y ∈ B ∪ A ∪ C, G.Adj v y := by rw [hUC]; exact hvS
  have hPavoid' : ∀ w ∈ v :: ((R₀.drop 0).take (j - 0 + 1)).reverse,
      w ∉ (B ∪ A ∪ C) ∪ ({b₀} : Set V) := by rw [hUC]; exact hPavoid
  have hQavoid' : ∀ w ∈ v :: (R₀.drop i).take (R₀.length - 1 - i + 1),
      w ∉ (B ∪ A ∪ C) ∪ ({a₀} : Set V) := by rw [hUC]; exact hQavoid
  have hPQint' : SPGT.Anticomplete G
      ({w : V | w ∈ SPGT.interior (v :: (R₀.drop i).take (R₀.length - 1 - i + 1))} ∪
        {w : V | w ∈ SPGT.interior (v :: ((R₀.drop 0).take (j - 0 + 1)).reverse)})
      (B ∪ A ∪ C) := by
    rw [hUC]
    rintro w (hw | hw)
    · exact hPQint w (Or.inr hw)
    · exact hPQint w (Or.inl hw)
  have hsecond : SPGT.VertexComplete G v A ∨ IsLeftStar G B C A v :=
    _root_.Workspace.Statements.S11.SPGT.thm_11_2 G hG hK4 B C A hswap.1.1 b₀ a₀ R₀.reverse
      hswap.1.2.1 v hvABC' hvS' ha
      (v :: (R₀.drop i).take (R₀.length - 1 - i + 1))
      (v :: ((R₀.drop 0).take (j - 0 + 1)).reverse) hQ hQavoid' hP hPavoid' hPQint'
  exact ⟨hfirst, hsecond⟩

/-! ### The application of 10.4

PAPER: *"Let `a₁`-`R₁`-`b₁`, `a₂`-`R₂`-`b₂` be a step; then by 10.4, `v` has no neighbour in
`R₁ \ a₁` or in `R₂ \ a₂`, and therefore `v` is a left-star."* -/
private theorem leftStar_of_ACompleteMinor {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hS : StepConnected G A C B) (hban : IsBanister G A C B a₀ R₀ b₀)
    (v : V) (hv : v ∉ staircaseVertices A C B R₀)
    (hnoR₀ : ∀ y ∈ R₀, ¬ G.Adj v y)
    (hAc : SPGT.VertexComplete G v A) :
    IsLeftStar G A C B v := by
  classical
  have hvABC : v ∉ A ∪ B ∪ C := fun h => hv (Set.mem_union_right _ h)
  have hvR0 : v ∉ R₀ := fun h => hv (Set.mem_union_left _ h)
  refine ⟨hvABC, hAc, ?_⟩
  intro w hwBC hadjw
  have hwS : w ∈ A ∪ B ∪ C := by
    rcases hwBC with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  obtain ⟨c₁, S₁, d₁, c₂, S₂, d₂, hstep0, hmem0⟩ := hS.2.2.2.1 w hwS
  -- the argument for a step whose *first* rung contains `w`
  have main : ∀ (a₁ b₁ a₂ b₂ : V) (R₁ R₂ : List V),
      IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂ → w ∈ R₁ → False := by
    intro a₁ b₁ a₂ b₂ R₁ R₂ hstep hwR₁
    obtain ⟨hr1, hr2, hdis, hedge⟩ := id hstep
    have ha₁R₁ : a₁ ∈ R₁ := (PathBasics.isPathFrom_ends_mem hr1.1).1
    have hb₁R₁ : b₁ ∈ R₁ := (PathBasics.isPathFrom_ends_mem hr1.1).2
    have ha₂R₂ : a₂ ∈ R₂ := (PathBasics.isPathFrom_ends_mem hr2.1).1
    have hb₂R₂ : b₂ ∈ R₂ := (PathBasics.isPathFrom_ends_mem hr2.1).2
    have hform : FormPrism G ![a₁, a₂, a₀] ![b₁, b₂, b₀] R₁ R₂ R₀ :=
      PrismFromBanisterAndStep.formPrism_of_banister_and_step hban hstep
    set aa : Fin 3 → V := ![a₁, a₂, a₀] with haa
    set bb : Fin 3 → V := ![b₁, b₂, b₀] with hbb
    set RR : Fin 3 → List V := ![R₁, R₂, R₀] with hRR
    have hRR0 : RR 0 = R₁ := by simp [hRR]
    have hRR1 : RR 1 = R₂ := by simp [hRR]
    have hRR2 : RR 2 = R₀ := by simp [hRR]
    have haa0 : aa 0 = a₁ := by simp [haa]
    have haa1 : aa 1 = a₂ := by simp [haa]
    have haa2 : aa 2 = a₀ := by simp [haa]
    have hbb0 : bb 0 = b₁ := by simp [hbb]
    have hbb1 : bb 1 = b₂ := by simp [hbb]
    have hbb2 : bb 2 = b₀ := by simp [hbb]
    have hformR : FormPrism G aa bb (RR 0) (RR 1) (RR 2) := by
      rw [hRR0, hRR1, hRR2]; exact hform
    obtain ⟨K, hK⟩ : ∃ K : Set V,
        K = {y : V | y ∈ RR 0} ∪ {y : V | y ∈ RR 1} ∪ {y : V | y ∈ RR 2} := ⟨_, rfl⟩
    have hmemK : ∀ y : V, y ∈ K ↔ (y ∈ R₁ ∨ y ∈ R₂ ∨ y ∈ R₀) := by
      intro y
      rw [hK, hRR0, hRR1, hRR2]
      simp only [Set.mem_union, Set.mem_setOf_eq]
      tauto
    -- `v` is not on the prism
    have hvK : v ∉ K := by
      rw [hmemK]
      rintro (h | h | h)
      · exact hvABC (rung_mem_strip hr1 v h)
      · exact hvABC (rung_mem_strip hr2 v h)
      · exact hvR0 h
    have hFK : ({v} : Set V) ⊆ Kᶜ := by
      intro y hy
      rw [(hy : y = v)]
      exact hvK
    have hFconn : SPGT.ConnectedSet G ({v} : Set V) := by
      intro p q
      have hpq : p = q := Subtype.ext (p.2.trans q.2.symm)
      rw [hpq]
    have hFmaj : IsEvenPrism G aa bb (RR 0) (RR 1) (RR 2) →
        ∀ z ∈ ({v} : Set V), ¬ MajorForPrism G aa bb z :=
      fun hev => absurd ⟨aa, bb, RR 0, RR 1, RR 2, hev⟩ hprism
    -- the three attachments the paper points at
    have hatt : ∀ y : V, (y ∈ R₁ ∨ y ∈ R₂ ∨ y ∈ R₀) → G.Adj v y →
        y ∈ attachments G ({v} : Set V) K := by
      intro y hyK hyadj
      exact ⟨(hmemK y).mpr hyK, v, rfl, hyadj.symm⟩
    have ha₁att : a₁ ∈ attachments G ({v} : Set V) K :=
      hatt a₁ (Or.inl ha₁R₁) (hAc a₁ hr1.2.1)
    have ha₂att : a₂ ∈ attachments G ({v} : Set V) K :=
      hatt a₂ (Or.inr (Or.inl ha₂R₂)) (hAc a₂ hr2.2.1)
    have hwatt : w ∈ attachments G ({v} : Set V) K := hatt w (Or.inl hwR₁) hadjw
    -- the attachment set is not local
    have hFloc : ¬ LocalForPrism aa bb (RR 0) (RR 1) (RR 2)
        (attachments G ({v} : Set V) K) := by
      rw [hRR0, hRR1, hRR2]
      rintro (h | h | h | h | h)
      · exact hdis a₂ (h ha₂att) ha₂R₂
      · exact hdis a₁ ha₁R₁ (h ha₁att)
      · exact hban.2.1 a₁ (h ha₁att) (Or.inl (Or.inl hr1.2.1))
      · rw [haa0, haa1, haa2] at h
        have hw3 : w = a₁ ∨ w = a₂ ∨ w = a₀ := by
          have := h hwatt
          simpa using this
        rcases hw3 with rfl | rfl | rfl
        · rcases hwBC with hh | hh
          · exact Set.disjoint_left.mp hS.1.1 hr1.2.1 hh
          · exact Set.disjoint_left.mp hS.1.2.1 hr1.2.1 hh
        · rcases hwBC with hh | hh
          · exact Set.disjoint_left.mp hS.1.1 hr2.2.1 hh
          · exact Set.disjoint_left.mp hS.1.2.1 hr2.2.1 hh
        · exact hban.2.2.1.1 hwS
      · rw [hbb0, hbb1, hbb2] at h
        have ha3 : a₁ = b₁ ∨ a₁ = b₂ ∨ a₁ = b₀ := by
          have := h ha₁att
          simpa using this
        rcases ha3 with hh | hh | hh
        · exact Set.disjoint_left.mp hS.1.1 hr1.2.1 (hh ▸ hr1.2.2.1)
        · exact Set.disjoint_left.mp hS.1.1 hr1.2.1 (hh ▸ hr2.2.2.1)
        · exact hban.2.2.2.1.1 (Or.inl (Or.inl (hh ▸ hr1.2.1)))
    -- no attachment lies on the banister
    have hR₃ : ∀ y ∈ attachments G ({v} : Set V) K, y ∉ RR 2 := by
      intro y hy hyR
      rw [hRR2] at hyR
      obtain ⟨-, f, hf, hadjf⟩ := hy
      rw [(hf : f = v)] at hadjf
      exact hnoR₀ y hyR hadjf.symm
    have h104 := _root_.Workspace.Statements.S10.SPGT.thm_10_4 G hG
      (by rintro ⟨n, H, K', happ, -⟩; exact hK4 ⟨n, H, K', happ⟩)
      aa bb RR K ({v} : Set V) hformR hK hFK hFconn hFmaj hFloc hR₃
    exact Set.not_nontrivial_singleton h104.1
  rcases hmem0 with h | h
  · exact main c₁ d₁ c₂ d₂ S₁ S₂ hstep0 h
  · exact main c₂ d₂ c₁ d₁ S₂ S₁ (step_symm hstep0) h

/-- **12.1 (4)**: *"If `v` is nonadjacent to both `a₀, b₀` then the theorem holds."* -/
theorem thm121Case4 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    (v : V) (hv : v ∉ staircaseVertices A C B R₀)
    (ha : ¬ G.Adj v a₀) (hb : ¬ G.Adj v b₀) :
    (MinorForStaircase G A C B a₀ R₀ b₀ v ∧
        (IsLeftStar G A C B v ∨ ¬ SPGT.VertexComplete G v A) ∧
        (IsRightStar G A C B v ∨ ¬ SPGT.VertexComplete G v B)) ∨
      (MajorForStaircase G A C B a₀ R₀ b₀ v ∧
        (LeftDiagonal G A C B a₀ R₀ b₀ v ∨ RightDiagonal G A C B a₀ R₀ b₀ v ∨
          CentralForStaircase G A C B a₀ R₀ b₀ v)) ∨
      ((IsLeftStar G A C B v ∧ ∃ x ∈ R₀, x ≠ a₀ ∧ G.Adj v x) ∨
        (IsRightStar G A C B v ∧ ∃ x ∈ R₀, x ≠ b₀ ∧ G.Adj v x)) := by
  classical
  have hS : StepConnected G A C B := hK.1.1
  have hban : IsBanister G A C B a₀ R₀ b₀ := hK.1.2.1
  have hUC : B ∪ A ∪ C = A ∪ B ∪ C := by rw [Set.union_comm B A]
  by_cases hVS : ∃ y ∈ A ∪ B ∪ C, G.Adj v y
  · by_cases hR0 : ∃ y ∈ R₀, G.Adj v y
    · -- PAPER: *"Suppose first that `v` also has a neighbour in `R₀*`."*
      obtain ⟨x, hxR₀, hvx⟩ := hR0
      have hxa : x ≠ a₀ := by rintro rfl; exact ha hvx
      have hxb : x ≠ b₀ := by rintro rfl; exact hb hvx
      have hxint : x ∈ SPGT.interior R₀ :=
        (PathBasics.mem_interior_iff_of_pathFrom hban.1).mpr ⟨hxR₀, hxa, hxb⟩
      obtain ⟨hL, hR⟩ := case4Link G hG hK4 A C B a₀ b₀ R₀ hK v hv hVS ha hb ⟨x, hxint, hvx⟩
      rcases hL with hBc | hls
      · rcases hR with hAc | hrs
        · -- PAPER: *"and therefore central, and statement 2 holds"*
          refine Or.inr (Or.inl ⟨⟨hv, ?_, ?_, x, hxR₀, hvx⟩, Or.inr (Or.inr ⟨hv, ?_, ha, hb⟩)⟩)
          · obtain ⟨p, hp⟩ := hS.2.1.1
            exact ⟨p, hp, hAc p hp⟩
          · obtain ⟨q, hq⟩ := hS.2.1.2
            exact ⟨q, hq, hBc q hq⟩
          · rintro y (hy | hy)
            · exact hAc y hy
            · exact hBc y hy
        · -- the reflected form of *"if `v` is a left-star then statement 3 holds"*
          refine Or.inr (Or.inr (Or.inr ⟨⟨?_, hrs.2.1, hrs.2.2⟩, x, hxR₀, hxb, hvx⟩))
          rw [← hUC]; exact hrs.1
      · -- PAPER: *"If `v` is a left-star then statement 3 holds"*
        exact Or.inr (Or.inr (Or.inl ⟨hls, x, hxR₀, hxa, hvx⟩))
    · -- PAPER: *"Thus we may assume that `v` has no neighbour in `V(R₀)`, and therefore `v` is
      -- minor.  We claim that statement 1 holds …"*
      push_neg at hR0
      have hswap : MaximalStaircase G B C A b₀ R₀.reverse a₀ :=
        Thm121Symmetry.thm121SwapStaircase G A C B a₀ b₀ R₀ hK
      refine Or.inl ⟨⟨hv, Or.inl ?_⟩, ?_, ?_⟩
      · rintro y ⟨hadj, hy | hy⟩
        · exact absurd hadj (hR0 y hy)
        · exact hy
      · -- *"to show this we may assume that `v` is `A`-complete … therefore `v` is a left-star"*
        by_cases hAc : SPGT.VertexComplete G v A
        · exact Or.inl (leftStar_of_ACompleteMinor G hG hK4 hprism A C B a₀ b₀ R₀ hS hban v hv
            hR0 hAc)
        · exact Or.inr hAc
      · -- the same, reflected
        by_cases hBc : SPGT.VertexComplete G v B
        · refine Or.inl ?_
          have hv' : v ∉ staircaseVertices B C A R₀.reverse := by
            rw [Thm121Symmetry.thm121SwapVertices A C B R₀]; exact hv
          have hR0' : ∀ y ∈ R₀.reverse, ¬ G.Adj v y := fun y hy =>
            hR0 y (List.mem_reverse.mp hy)
          have := leftStar_of_ACompleteMinor G hG hK4 hprism B C A b₀ a₀ R₀.reverse
            hswap.1.1 hswap.1.2.1 v hv' hR0' hBc
          exact ⟨by rw [← hUC]; exact this.1, this.2.1, this.2.2⟩
        · exact Or.inr hBc
  · -- PAPER: *"we may assume that `v` has a neighbour in `V(S)`, since otherwise it is minor"*
    push_neg at hVS
    exact Or.inl (Thm121MinorCriteria.thm121AltOneOfNoStripNeighbour G A C B a₀ b₀ R₀ hS v hv
      hVS)

end Workspace.ProofLemmas.Thm121Case4
