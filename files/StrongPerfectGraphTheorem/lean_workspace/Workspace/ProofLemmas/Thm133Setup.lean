/-  **13.3 — the printed setting and its supporting library.**

    This module is the importable lift of the complete (fully proved) support library
    developed in
    `ProofAttempts/thm_13_3/Attempt_4.lean`.  It covers the printed opening paragraph of the
    proof of 13.3 (printed p. 83)

      *"Let `(K, x₁)` be a 3-breaker, where `K = (S = (A, C, B), a₀-R₀-b₀)`.  The 1-vertex
      sequence `x₁` is a right-sequence; so there exists a right-sequence `x₁, …, x_t` of
      maximum length, with `t ≥ 1`.  Let `X = {x₁, …, x_t}`, and let `Y` be the set of all
      `A ∪ X`-complete vertices in `V(G) \ V(S)`.  So `a₀ ∈ Y` by 13.2."*

    together with `major_diagonal_or_central` (the 12.1 trichotomy used inside claim (1)) and
    the bookkeeping about `X ∪ Y ∪ B` that the closing paragraph needs.

    The import list is deliberately minimal: the eight statement modules that
    `Attempt_4.lean` imported but never used are dropped, since the full closure exhausts the
    LSP's memory budget.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.LongOddPrism
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.Types.Appearances
import Workspace.Types.SkewTools
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.Thm134RegionAux
import Workspace.ProofLemmas.StaircaseLeftRightSymmetry
import Workspace.Statements.S12.Thm_12_1
import Workspace.Statements.S13.Thm_13_2

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm133Setup

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.SkewTools Workspace.Types.SkewTools.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Small facts about a step-connected strip -/

/-- Prepending a vertex adjacent to the head of a path and to nothing else on it. -/
theorem isPathFrom_cons {G : SimpleGraph V} {S : List V} {w₀ w₁ z : V}
    (hS : IsPathFrom G S w₀ w₁) (hz : z ∉ S)
    (hadj : ∀ y ∈ S, (G.Adj z y ↔ y = w₀)) :
    IsPathFrom G (z :: S) z w₁ := by
  have h := PathGlue.glue_path (R := [z]) (S := S) (u₀ := z) (u₁ := z)
    ⟨PathBasics.isPathList_singleton G z, by simp, by simp⟩ hS
    (by intro x hx; simp at hx; subst hx; exact hz)
    (by
      intro x hx y hy
      simp at hx
      subst hx
      simpa using hadj y hy)
  simpa using h

/-- Every `B`-complete vertex lies outside the strip. -/
theorem bComplete_not_mem_strip {G : SimpleGraph V} {A C B : Set V}
    (hS : StepConnected G A C B) {v : V} (hv : VertexComplete G v B) :
    v ∉ A ∪ B ∪ C := by
  obtain ⟨⟨hAB, hAC, hBC⟩, ⟨hAne, hBne⟩, hrung, hstep, hpart⟩ := hS
  intro hmem
  -- the vertex lies in a step
  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstp, hvin⟩ := hstep v hmem
  obtain ⟨hr1, hr2, hdisj, hcross⟩ := hstp
  have hb₁ : b₁ ∈ R₁ := PathBasics.getLast_mem hr1.1.2.2
  have hb₂ : b₂ ∈ R₂ := PathBasics.getLast_mem hr2.1.2.2
  have ha₁ : a₁ ∈ R₁ := PathBasics.head_mem hr1.1.2.1
  have ha₂ : a₂ ∈ R₂ := PathBasics.head_mem hr2.1.2.1
  rcases hvin with hv1 | hv2
  · -- `v ∈ R₁`; `v` is adjacent to `b₂ ∈ B`, so `v = b₁` and `b₂ = b₂`, or `v = a₁, b₂ = a₂`
    have hadj : G.Adj v b₂ := hv b₂ hr2.2.2.1
    rcases (hcross v hv1 b₂ hb₂).mp hadj with ⟨hva, hba⟩ | ⟨hvb, -⟩
    · -- `b₂ = a₂`, impossible since `A` and `B` are disjoint
      exact (Set.disjoint_left.mp hAB hr2.2.1) (hba ▸ hr2.2.2.1)
    · -- `v = b₁ ∈ B`, but `v` is `B`-complete
      exact G.irrefl (hvb ▸ hv v (hvb ▸ hr1.2.2.1))
  · have hadj : G.Adj v b₁ := hv b₁ hr1.2.2.1
    have hadj' : G.Adj b₁ v := hadj.symm
    rcases (hcross b₁ hb₁ v hv2).mp hadj' with ⟨hb1a, hva⟩ | ⟨-, hvb⟩
    · -- `b₁ = a₁`, impossible
      exact (Set.disjoint_left.mp hAB hr1.2.1) (hb1a ▸ hr1.2.2.1)
    · exact G.irrefl (hvb ▸ hv v (hvb ▸ hr2.2.2.1))

/-- The strip of a staircase read backwards.  (`StaircaseLeftRightSymmetry.stepConnected_swap`
is `private`; the public `maximalStaircase_swap` carries it.) -/
theorem stepConnected_swap' {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    (hK : MaximalStaircase G A C B a₀ R₀ b₀) : StepConnected G B C A :=
  (StaircaseLeftRightSymmetry.maximalStaircase_swap.mp hK).1.1

/-- `A ∪ C` is connected (the mirror of `Thm134RegionAux.stripFarSideConnected`). -/
theorem nearSideConnected {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    (hK : MaximalStaircase G A C B a₀ R₀ b₀) : ConnectedSet G (A ∪ C) := by
  have h := Thm134RegionAux.stripFarSideConnected (stepConnected_swap' hK)
  simpa [Set.union_comm] using h

/-- Every vertex of `B` is the far end of some rung. -/
theorem rung_of_mem_B {G : SimpleGraph V} {A C B : Set V}
    (hS : StepConnected G A C B) {b : V} (hb : b ∈ B) :
    ∃ (a : V) (R : List V), IsRungOfStrip G A C B a R b := by
  obtain ⟨a, p, b', hr, hmem⟩ := hS.2.2.1 b (Or.inl (Or.inr hb))
  have : b = b' := hr.2.2.2.2.1 b hmem hb
  exact ⟨a, p, this ▸ hr⟩

/-- Every vertex of `B` has a neighbour in `A ∪ C`. -/
theorem bVertex_has_neighbour_in_AC {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V}
    {R₀ : List V} (hK : MaximalStaircase G A C B a₀ R₀ b₀) :
    ∀ b ∈ B, ∃ z ∈ A ∪ C, G.Adj b z :=
  Thm134RegionAux.stripVertexHasFarNeighbour (stepConnected_swap' hK)

/-! ### Right-sequences -/

/-- Adding one vertex at the end of a right-sequence. -/
theorem rightSequence_snoc {G : SimpleGraph V} {A C B : Set V} {x : List V} {v : V}
    (hx : IsRightSequence G A C B x) (hvx : v ∉ x)
    (hvB : VertexComplete G v B)
    (h2 : VertexComplete G v A → ∃ y ∈ x, ¬ G.Adj y v)
    (h3 : VertexAnticomplete G v A → ∃ (r : V) (R : List V), IsBanister G A C B r R v ∧
        ∃ y ∈ x, ¬ G.Adj r y) :
    IsRightSequence G A C B (x ++ [v]) := by
  obtain ⟨⟨hnd, hB⟩, hax2, hax3⟩ := hx
  have hlen : (x ++ [v]).length = x.length + 1 := by simp
  have hget : ∀ (i : ℕ) (hi : i < (x ++ [v]).length),
      (∃ h : i < x.length, (x ++ [v])[i] = x[i]'h) ∨
        (i = x.length ∧ (x ++ [v])[i] = v) := by
    intro i hi
    rcases lt_or_ge i x.length with h | h
    · exact Or.inl ⟨h, List.getElem_append_left h⟩
    · have hix : i = x.length := by omega
      subst hix
      refine Or.inr ⟨rfl, ?_⟩
      simp
  have htake : ∀ (i : ℕ), i ≤ x.length → (x ++ [v]).take i = x.take i := by
    intro i hi
    exact List.take_append_of_le_length hi
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [List.nodup_append, List.nodup_cons, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_self, List.disjoint_singleton, true_and]
    refine ⟨hnd, ?_⟩
    rintro a ha b hb rfl
    simp only [List.mem_singleton] at hb
    exact hvx (hb ▸ ha)
  · intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact hB w h
    · simpa [List.mem_singleton.mp h] using hvB
  · intro i hi hcomp
    rcases hget i hi with ⟨hix, he⟩ | ⟨hix, he⟩
    · rw [he] at hcomp ⊢
      obtain ⟨y, hy, hny⟩ := hax2 i hix hcomp
      exact ⟨y, by rw [htake i (by omega)]; exact hy, hny⟩
    · rw [he] at hcomp ⊢
      obtain ⟨y, hy, hny⟩ := h2 hcomp
      refine ⟨y, ?_, hny⟩
      rw [htake i (by omega), hix, List.take_length]
      exact hy
  · intro i hi hanti
    rcases hget i hi with ⟨hix, he⟩ | ⟨hix, he⟩
    · rw [he] at hanti ⊢
      obtain ⟨r, R, hban, y, hy, hny⟩ := hax3 i hix hanti
      exact ⟨r, R, hban, y, by rw [htake i (by omega)]; exact hy, hny⟩
    · rw [he] at hanti ⊢
      obtain ⟨r, R, hban, y, hy, hny⟩ := h3 hanti
      refine ⟨r, R, hban, y, ?_, hny⟩
      rw [htake i (by omega), hix, List.take_length]
      exact hy

/-- A right-sequence of maximum length. -/
theorem exists_max_rightSequence {G : SimpleGraph V} {A C B : Set V} {x₀ : List V}
    (h : IsRightSequence G A C B x₀) :
    ∃ x : List V, IsRightSequence G A C B x ∧ x₀.length ≤ x.length ∧
      ∀ y : List V, IsRightSequence G A C B y → y.length ≤ x.length := by
  classical
  set P : ℕ → Prop := fun n => ∃ y : List V, IsRightSequence G A C B y ∧ y.length = n with hP
  have hbound : ∀ n, P n → n ≤ Fintype.card V := by
    rintro n ⟨y, hy, rfl⟩
    exact hy.1.1.length_le_card
  have hP0 : P x₀.length := ⟨x₀, h, rfl⟩
  have hle : x₀.length ≤ Fintype.card V := hbound _ hP0
  obtain ⟨x, hx, hxlen⟩ := Nat.findGreatest_spec (P := P) hle hP0
  refine ⟨x, hx, ?_, ?_⟩
  · rw [hxlen]; exact Nat.le_findGreatest hle hP0
  · intro y hy
    rw [hxlen]
    exact Nat.le_findGreatest (hbound _ ⟨y, hy, rfl⟩) ⟨y, hy, rfl⟩

/-! ### The chain of predecessors (the paper's trajectory, truncated)

PAPER (13.3, printed p. 83): *"Let `v`-`w₁`-⋯-`w_n` be the trajectory of `v` … there is a
minimum `i` with `1 ≤ i ≤ n` such that `w_i` is not left-diagonal.  By 12.5 applied to the
sequence `v, w₁, …, w_i` …"*.  Only the initial segment `w₁, …, w_i` of the trajectory is ever
used, so it is built directly: follow predecessors from the earliest nonneighbour of `v` in `X`
and stop at the first term that is not left-diagonal.  The second right-sequence axiom supplies
each predecessor, and terminates the recursion because `x₀` is never `A`-complete. -/

/-- The chain of predecessors starting at `x_i`, stopped at the first term failing `LD`.
It is an antipath because the predecessor of a term is its *earliest* nonneighbour. -/
theorem exists_predecessor_chain {G : SimpleGraph V} {A C B : Set V} {x : List V}
    (hx : IsRightSequence G A C B x) (LD : V → Prop)
    (hLD : ∀ w : V, LD w → VertexComplete G w A) :
    ∀ (i : ℕ) (hi : i < x.length),
      ∃ (L : List V) (j : ℕ) (hj : j < x.length),
        IsAntipathFrom G L (x[i]'hi) (x[j]'hj) ∧
        (∀ w ∈ L, ∃ (k : ℕ) (hk : k < x.length), k ≤ i ∧ x[k]'hk = w) ∧
        (∀ w ∈ L, w ≠ x[j]'hj → LD w) ∧
        ¬ LD (x[j]'hj) := by
  classical
  intro i
  induction i using Nat.strong_induction_on with
  | _ i IH =>
    intro hi
    by_cases hLDi : LD (x[i]'hi)
    · -- follow the predecessor
      have hcomp : VertexComplete G (x[i]'hi) A := hLD _ hLDi
      obtain ⟨y, hy, hny⟩ := hx.2.1 i hi hcomp
      -- turn the membership in `x.take i` into an index below `i`
      have hQ : ∃ k : ℕ, ∃ hk : k < x.length, k < i ∧ ¬ G.Adj (x[k]'hk) (x[i]'hi) := by
        obtain ⟨k, hk, hkval⟩ := List.mem_iff_getElem.mp hy
        have hklen : k < (x.take i).length := hk
        rw [List.length_take] at hklen
        have hkx : k < x.length := by omega
        have hki : k < i := by omega
        refine ⟨k, hkx, hki, ?_⟩
        have : (x.take i)[k]'hk = x[k]'hkx := List.getElem_take
        rw [this] at hkval
        rw [hkval]
        exact hny
      set Q : ℕ → Prop := fun k => ∃ hk : k < x.length, k < i ∧ ¬ G.Adj (x[k]'hk) (x[i]'hi)
        with hQdef
      have hQex : ∃ k, Q k := hQ
      obtain ⟨hhx, hhi, hhadj⟩ := Nat.find_spec hQex
      set h := Nat.find hQex with hhdef
      have hmin : ∀ k : ℕ, k < h → ∀ hk : k < x.length, G.Adj (x[k]'hk) (x[i]'hi) := by
        intro k hkh hk
        have := Nat.find_min hQex hkh
        by_contra hcon
        exact this ⟨hk, by omega, hcon⟩
      obtain ⟨L', j, hj, hL', hidx', hLD', hnLD'⟩ := IH h hhi hhx
      -- every vertex of `L'` other than its head sits at an index `< h`
      have hidxlt : ∀ w ∈ L', w ≠ x[h]'hhx → ∃ (k : ℕ) (hk : k < x.length), k < h ∧ x[k]'hk = w := by
        intro w hw hwne
        obtain ⟨k, hk, hkh, hkw⟩ := hidx' w hw
        refine ⟨k, hk, ?_, hkw⟩
        rcases lt_or_eq_of_le hkh with h1 | h1
        · exact h1
        · exfalso
          apply hwne
          have heq : x[k]'hk = x[h]'hhx := by subst h1; rfl
          rw [← hkw, heq]
      have hxinotL' : (x[i]'hi) ∉ L' := by
        intro hmem
        obtain ⟨k, hk, hkh, hkw⟩ := hidx' _ hmem
        have hne : k ≠ i := by omega
        exact hne (List.Nodup.getElem_inj_iff hx.1.1 |>.mp hkw)
      have hcons : ∀ y ∈ L', (Gᶜ.Adj (x[i]'hi) y ↔ y = x[h]'hhx) := by
        intro y hy
        constructor
        · intro hadj
          by_contra hyne
          obtain ⟨k, hk, hkh, hkw⟩ := hidxlt y hy hyne
          have : G.Adj (x[k]'hk) (x[i]'hi) := hmin k hkh hk
          rw [hkw] at this
          exact (SimpleGraph.compl_adj G _ _).mp hadj |>.2 this.symm
        · intro hyh
          subst hyh
          refine (SimpleGraph.compl_adj G _ _).mpr ⟨?_, ?_⟩
          · intro hcon
            have : i = h := (List.Nodup.getElem_inj_iff hx.1.1).mp hcon
            omega
          · intro hcon
            exact hhadj hcon.symm
      have hpath : IsPathFrom Gᶜ ((x[i]'hi) :: L') (x[i]'hi) (x[j]'hj) :=
        isPathFrom_cons (G := Gᶜ) hL' hxinotL' hcons
      refine ⟨(x[i]'hi) :: L', j, hj, hpath, ?_, ?_, hnLD'⟩
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact ⟨i, hi, le_rfl, rfl⟩
        · obtain ⟨k, hk, hkh, hkw⟩ := hidx' w hw
          exact ⟨k, hk, by omega, hkw⟩
      · intro w hw hwne
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hLDi
        · exact hLD' w hw hwne
    · exact ⟨[x[i]'hi], i, hi,
        ⟨PathBasics.isPathList_singleton Gᶜ _, by simp, by simp⟩,
        by intro w hw; simp only [List.mem_singleton] at hw; exact ⟨i, hi, le_rfl, hw.symm⟩,
        by intro w hw hwne; simp only [List.mem_singleton] at hw; exact absurd hw hwne,
        hLDi⟩

/-- The paper's *"let `v`-`w₁`-⋯-`w_i` be the initial segment of the trajectory of `v` up to the
first term that is not left-diagonal"*: an antipath from `v` into `X`, whose interior consists of
terms of the right-sequence satisfying `LD`, and whose far end is a term failing `LD`. -/
theorem exists_chain_from_vertex {G : SimpleGraph V} {A C B : Set V} {x : List V}
    (hx : IsRightSequence G A C B x) (LD : V → Prop)
    (hLD : ∀ w : V, LD w → VertexComplete G w A)
    {v : V} (hvx : v ∉ x) (hvnc : ¬ VertexComplete G v {y : V | y ∈ x}) :
    ∃ (Q : List V) (z : V), IsAntipathFrom G Q v z ∧ z ∈ x ∧
      (∀ w ∈ SPGT.interior Q, w ∈ x ∧ LD w) ∧ ¬ LD z := by
  classical
  -- the earliest nonneighbour of `v` in `X`
  have hex : ∃ k : ℕ, ∃ hk : k < x.length, ¬ G.Adj v (x[k]'hk) := by
    rw [VertexComplete] at hvnc
    push_neg at hvnc
    obtain ⟨y, hy, hny⟩ := hvnc
    obtain ⟨k, hk, hkv⟩ := List.mem_iff_getElem.mp hy
    exact ⟨k, hk, by rw [hkv]; exact hny⟩
  set Q₀ : ℕ → Prop := fun k => ∃ hk : k < x.length, ¬ G.Adj v (x[k]'hk) with hQ₀
  have hQex : ∃ k, Q₀ k := hex
  obtain ⟨hi₀x, hi₀adj⟩ := Nat.find_spec hQex
  set i₀ := Nat.find hQex with hi₀def
  have hmin : ∀ k : ℕ, k < i₀ → ∀ hk : k < x.length, G.Adj v (x[k]'hk) := by
    intro k hki hk
    have := Nat.find_min hQex hki
    by_contra hcon
    exact this ⟨hk, hcon⟩
  obtain ⟨L, j, hj, hL, hidx, hLD', hnLD⟩ := exists_predecessor_chain hx LD hLD i₀ hi₀x
  have hmemx : ∀ w ∈ L, w ∈ x := by
    intro w hw
    obtain ⟨k, hk, -, hkw⟩ := hidx w hw
    exact hkw ▸ List.getElem_mem hk
  have hvnotL : v ∉ L := fun hmem => hvx (hmemx v hmem)
  have hcons : ∀ y ∈ L, (Gᶜ.Adj v y ↔ y = x[i₀]'hi₀x) := by
    intro y hy
    constructor
    · intro hadj
      by_contra hyne
      obtain ⟨k, hk, hki, hkw⟩ := hidx y hy
      have hki' : k < i₀ := by
        rcases lt_or_eq_of_le hki with h1 | h1
        · exact h1
        · exfalso
          apply hyne
          have heq : x[k]'hk = x[i₀]'hi₀x := by subst h1; rfl
          rw [← hkw, heq]
      have := hmin k hki' hk
      rw [hkw] at this
      exact ((SimpleGraph.compl_adj G _ _).mp hadj).2 this
    · intro hyh
      subst hyh
      exact (SimpleGraph.compl_adj G _ _).mpr
        ⟨fun hcon => hvx (hcon ▸ List.getElem_mem hi₀x), hi₀adj⟩
  have hpath : IsPathFrom Gᶜ (v :: L) v (x[j]'hj) := isPathFrom_cons (G := Gᶜ) hL hvnotL hcons
  refine ⟨v :: L, x[j]'hj, hpath, List.getElem_mem hj, ?_, hnLD⟩
  intro w hw
  rw [PathBasics.mem_interior_iff_of_pathFrom hpath] at hw
  obtain ⟨hwmem, hwv, hwz⟩ := hw
  rcases List.mem_cons.mp hwmem with rfl | hwL
  · exact absurd rfl hwv
  · exact ⟨hmemx w hwL, hLD' w hwL hwz⟩

/-- The two ends of a path of length `≥ 2` are nonadjacent. -/
theorem ends_not_adj {G : SimpleGraph V} {p : List V} {u v : V} (h : IsPathFrom G p u v)
    (hlen : 2 ≤ pathLength p) : ¬ G.Adj u v := by
  have hlen' : 3 ≤ p.length := by
    have := PathBasics.length_eq_pathLength_add_one h.1; omega
  have h0 : p[0]'(by omega) = u := PathBasics.getElem_zero_of_head? h.2.1 (by omega)
  have hl : p[p.length - 1]'(by omega) = v := PathBasics.getElem_last_of_getLast? h.2.2 (by omega)
  have := PathBasics.path_ends_not_adj h.1 hlen'
  rwa [h0, hl] at this

/-! ### Where the terms of the right-sequence live -/

/-- A `B`-complete vertex adjacent to `a₀` is outside `V(K)`.  PAPER: *"Note that `b₀ ∉ X` by
13.2"* — and the terms of `X` are `B`-complete, so they miss the strip as well. -/
theorem not_mem_staircaseVertices {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V}
    {R₀ : List V} (hK : IsStaircase G A C B a₀ R₀ b₀)
    {v : V} (hvB : VertexComplete G v B) (hva₀ : G.Adj v a₀) :
    v ∉ staircaseVertices A C B R₀ := by
  obtain ⟨hSC, hban, hlen⟩ := hK
  obtain ⟨b, hb⟩ := hSC.2.1.2
  rintro (hmem | hmem)
  · -- `v ∈ V(R₀)`
    by_cases hva : v = a₀
    · exact hban.2.2.1.2.2 b (Or.inl hb) (hva ▸ hvB b hb)
    by_cases hvb : v = b₀
    · exact ends_not_adj hban.1 (by omega) ((hvb ▸ hva₀ : G.Adj b₀ a₀).symm)
    · exact hban.2.2.2.2 v
        ((PathBasics.mem_interior_iff_of_pathFrom hban.1).mpr ⟨hmem, hva, hvb⟩)
        b (Or.inl (Or.inr hb)) (hvB b hb)
  · exact bComplete_not_mem_strip hSC hvB hmem

/-! ### Major vertices -/

/-- A major vertex is not minor. -/
theorem not_minor_of_major {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    (hK : IsStaircase G A C B a₀ R₀ b₀) {v : V}
    (hmaj : MajorForStaircase G A C B a₀ R₀ b₀ v) :
    ¬ MinorForStaircase G A C B a₀ R₀ b₀ v := by
  obtain ⟨hSC, hban, hlen⟩ := hK
  obtain ⟨-, ⟨p, hp, hvp⟩, ⟨q, hq, hvq⟩, ⟨r, hr, hvr⟩⟩ := hmaj
  rintro ⟨-, hloc⟩
  have hmemp : p ∈ G.neighborSet v ∩ staircaseVertices A C B R₀ :=
    ⟨hvp, Or.inr (Or.inl (Or.inl hp))⟩
  have hmemq : q ∈ G.neighborSet v ∩ staircaseVertices A C B R₀ :=
    ⟨hvq, Or.inr (Or.inl (Or.inr hq))⟩
  have hmemr : r ∈ G.neighborSet v ∩ staircaseVertices A C B R₀ := ⟨hvr, Or.inl hr⟩
  have hrS : r ∉ A ∪ B ∪ C := hban.2.1 r hr
  rcases hloc with h | h | h | h
  · exact hrS (h hmemr)
  · -- `p ∈ A` cannot lie on `R₀`
    exact hban.2.1 p (h hmemp) (Or.inl (Or.inl hp))
  · -- `q ∈ B` cannot lie in `A ∪ {a₀}`
    rcases h hmemq with hqA | hqa
    · exact (Set.disjoint_left.mp hSC.1.1 hqA) hq
    · exact hban.2.2.1.1 (Or.inl (Or.inr ((hqa : q = a₀) ▸ hq)))
  · -- `p ∈ A` cannot lie in `B ∪ {b₀}`
    rcases h hmemp with hpB | hpb
    · exact (Set.disjoint_left.mp hSC.1.1 hp) hpB
    · exact hban.2.2.2.1.1 (Or.inl (Or.inl ((hpb : p = b₀) ▸ hp)))

/-- PAPER: *"By 12.1 …, `v` is left-diagonal, and not right-diagonal"* — the first half: a major
vertex falls into alternative 2 of 12.1, so it is left- or right-diagonal or central. -/
theorem major_diagonal_or_central {G : SimpleGraph V} (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (h1br : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    {A C B : Set V} {a₀ b₀ : V} {R₀ : List V} (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    {v : V} (hv : v ∉ staircaseVertices A C B R₀)
    (hmaj : MajorForStaircase G A C B a₀ R₀ b₀ v) :
    LeftDiagonal G A C B a₀ R₀ b₀ v ∨ RightDiagonal G A C B a₀ R₀ b₀ v ∨
      CentralForStaircase G A C B a₀ R₀ b₀ v := by
  obtain ⟨i, hi, -⟩ :=
    _root_.Workspace.Statements.S12.SPGT.thm_12_1 G hG hK4 hprism h1br A C B a₀ b₀ R₀ hK v hv
  fin_cases i
  · simp only [Matrix.cons_val_zero] at hi
    exact absurd hi.1 (not_minor_of_major hK.1 hmaj)
  · simpa only [Matrix.cons_val_one, Matrix.head_cons] using hi.2
  · simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hi
    exfalso
    obtain ⟨-, ⟨p, hp, hvp⟩, ⟨q, hq, hvq⟩, -⟩ := hmaj
    rcases hi with ⟨hls, -⟩ | ⟨hrs, -⟩
    · exact hls.2.2 q (Or.inl hq) hvq
    · exact hrs.2.2 p (Or.inl hp) hvp

/-! ## The setting of the printed proof of 13.3

PAPER: *"Let `(K, x₁)` be a 3-breaker, where `K = (S = (A, C, B), a₀-R₀-b₀)`.  The 1-vertex
sequence `x₁` is a right-sequence; so there exists a right-sequence `x₁, …, x_t` of maximum
length, with `t ≥ 1`.  Let `X = {x₁, …, x_t}`, and let `Y` be the set of all `A ∪ X`-complete
vertices in `V(G) \ V(S)`."* -/

/-- The ambient data of the printed proof: the hypotheses of 13.3 together with a
maximum-length right-sequence `x` for the staircase of the 3-breaker. -/
structure Ctx (G : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (x : List V) : Prop where
  berge : Berge G
  noK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4))
  noPrism : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G s t R₁ R₂ R₃
  no1br : ¬ ∃ A' C' B' F Q : Set V, IsOneBreaker G A' C' B' F Q
  no2br : ¬ ∃ (A' C' B' : Set V) (a' : V) (R' : List V) (b' : V) (Q : Set V),
      IsTwoBreaker G A' C' B' a' R' b' Q
  strongMax : StronglyMaximalStaircase G A C B a₀ R₀ b₀
  rseq : IsRightSequence G A C B x
  maximal : ∀ y : List V, IsRightSequence G A C B y → y.length ≤ x.length
  nonempty : x ≠ []

/-- `X = {x₁, …, x_t}`. -/
def Xs (x : List V) : Set V := {v : V | v ∈ x}

/-- `Y`, the set of all `A ∪ X`-complete vertices in `V(G) \ V(S)`. -/
def Ys (G : SimpleGraph V) (A C B : Set V) (x : List V) : Set V :=
  {v : V | v ∉ A ∪ B ∪ C ∧ VertexComplete G v (A ∪ Xs x)}

/-- The `B`-side `X ∪ Y ∪ B` of the skew partition the proof builds. -/
def Ws (G : SimpleGraph V) (A C B : Set V) (x : List V) : Set V :=
  Xs x ∪ Ys G A C B x ∪ B

namespace Ctx

variable {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V} {x : List V}

theorem staircase (c : Ctx G A C B a₀ b₀ R₀ x) : IsStaircase G A C B a₀ R₀ b₀ := c.strongMax.1.1

theorem maxStaircase (c : Ctx G A C B a₀ b₀ R₀ x) : MaximalStaircase G A C B a₀ R₀ b₀ :=
  c.strongMax.1

theorem stepConn (c : Ctx G A C B a₀ b₀ R₀ x) : StepConnected G A C B := c.staircase.1

theorem banister (c : Ctx G A C B a₀ b₀ R₀ x) : IsBanister G A C B a₀ R₀ b₀ := c.staircase.2.1

theorem lenR₀ (c : Ctx G A C B a₀ b₀ R₀ x) : 3 ≤ pathLength R₀ := c.staircase.2.2

theorem Ane (c : Ctx G A C B a₀ b₀ R₀ x) : A.Nonempty := c.stepConn.2.1.1

theorem Bne (c : Ctx G A C B a₀ b₀ R₀ x) : B.Nonempty := c.stepConn.2.1.2

theorem leftStar_a₀ (c : Ctx G A C B a₀ b₀ R₀ x) : IsLeftStar G A C B a₀ := c.banister.2.2.1

theorem rightStar_b₀ (c : Ctx G A C B a₀ b₀ R₀ x) : IsRightStar G A C B b₀ :=
  c.banister.2.2.2.1

/-- **13.2**: every term of the right-sequence is adjacent to `a₀`. -/
theorem adj_a₀ (c : Ctx G A C B a₀ b₀ R₀ x) : ∀ v ∈ x, G.Adj v a₀ :=
  _root_.Workspace.Statements.S13.SPGT.thm_13_2 G c.berge c.noK4 c.noPrism c.no1br c.no2br
    A C B a₀ b₀ R₀ c.strongMax x c.rseq

theorem xComplete (c : Ctx G A C B a₀ b₀ R₀ x) : ∀ v ∈ x, VertexComplete G v B :=
  c.rseq.1.2

/-- No term of the right-sequence lies in `V(K)`. -/
theorem x_not_mem_K (c : Ctx G A C B a₀ b₀ R₀ x) :
    ∀ v ∈ x, v ∉ staircaseVertices A C B R₀ :=
  fun v hv => not_mem_staircaseVertices c.staircase (c.xComplete v hv) (c.adj_a₀ v hv)

theorem X_nonempty (c : Ctx G A C B a₀ b₀ R₀ x) : (Xs x).Nonempty := by
  obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil x c.nonempty
  exact ⟨v, hv⟩

/-- PAPER: *"So `a₀ ∈ Y` by 13.2."* -/
theorem a₀_mem_Y (c : Ctx G A C B a₀ b₀ R₀ x) : a₀ ∈ Ys G A C B x := by
  refine ⟨c.leftStar_a₀.1, ?_⟩
  rintro y (hy | hy)
  · exact c.leftStar_a₀.2.1 y hy
  · exact (c.adj_a₀ y hy).symm

/-- PAPER: *"Note that `b₀ ∉ X` by 13.2, and so `b₀ ∉ X ∪ Y ∪ B` (since it is not
`A`-complete)."* -/
theorem b₀_not_mem_W (c : Ctx G A C B a₀ b₀ R₀ x) : b₀ ∉ Ws G A C B x := by
  obtain ⟨a, ha⟩ := c.Ane
  rintro ((hb | hb) | hb)
  · exact c.x_not_mem_K b₀ hb (Or.inl (PathBasics.getLast_mem c.banister.1.2.2))
  · exact hb.2 a (Or.inl ha) |> fun hadj => c.rightStar_b₀.2.2 a (Or.inl ha) hadj
  · exact c.rightStar_b₀.1 (Or.inl (Or.inr hb))

/-- Terms of the right-sequence are neither in `B` nor in `Y`. -/
theorem X_disjoint (c : Ctx G A C B a₀ b₀ R₀ x) :
    ∀ v ∈ Xs x, v ∉ Ys G A C B x ∧ v ∉ B := by
  intro v hv
  refine ⟨fun hy => G.irrefl (hy.2 v (Or.inr hv)), fun hb => ?_⟩
  exact G.irrefl (c.xComplete v hv v hb)

/-- PAPER: *"since `Y ∪ B` is complete to `X`"*. -/
theorem YB_complete_X (c : Ctx G A C B a₀ b₀ R₀ x) :
    ∀ v ∈ Ys G A C B x ∪ B, ∀ u ∈ Xs x, G.Adj v u := by
  rintro v (hv | hv) u hu
  · exact hv.2 u (Or.inr hu)
  · exact (c.xComplete u hu v hv).symm

/-- `A ∪ C` misses `X ∪ Y ∪ B`. -/
theorem AC_disjoint_W (c : Ctx G A C B a₀ b₀ R₀ x) : ∀ v ∈ A ∪ C, v ∉ Ws G A C B x := by
  rintro v hv ((hw | hw) | hw)
  · rcases hv with h | h
    · exact c.x_not_mem_K v hw (Or.inr (Or.inl (Or.inl h)))
    · exact c.x_not_mem_K v hw (Or.inr (Or.inr h))
  · rcases hv with h | h
    · exact hw.1 (Or.inl (Or.inl h))
    · exact hw.1 (Or.inr h)
  · rcases hv with h | h
    · exact (Set.disjoint_left.mp c.stepConn.1.1 h) hw
    · exact (Set.disjoint_left.mp c.stepConn.1.2.2 hw) h

/-- `A ∪ C` is connected. -/
theorem AC_connected (c : Ctx G A C B a₀ b₀ R₀ x) : ConnectedSet G (A ∪ C) :=
  nearSideConnected c.maxStaircase

end Ctx

end Workspace.ProofLemmas.Thm133Setup
