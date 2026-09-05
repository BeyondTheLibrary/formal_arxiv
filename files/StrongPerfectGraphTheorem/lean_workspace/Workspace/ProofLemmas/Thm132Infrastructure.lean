import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.LongOddPrism
import Workspace.Types.Appearances
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.Statements.S12.Thm_12_1
import Workspace.Statements.S12.Thm_12_5

set_option autoImplicit false

/-!
# Infrastructure for the proof of 13.2

This file contains only the finite-list bookkeeping suppressed in the printed
proof: initial segments of right-sequences, predecessor chains, and the
classification of a `B`-complete vertex outside a staircase.  The graph-theoretic
inputs are the already numbered results 12.1 and 12.5.
-/

namespace Workspace.ProofLemmas.Thm132Infrastructure

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Prepending a vertex adjacent (in the ambient graph) precisely to the old
head preserves an induced path. -/
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

/-- In an induced path on at least two vertices, the only neighbour of the
last end among the other path vertices is the penultimate vertex. -/
theorem adj_last_iff_eq_penultimate {G : SimpleGraph V} {p : List V} {u v z : V}
    (hp : IsPathFrom G p u v) (hlen : 2 ≤ p.length) (hz : z ∈ p) :
    G.Adj z v ↔ z = p[p.length - 2]'(by omega) := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hz
  have hlast : p[p.length - 1]'(by omega) = v :=
    PathBasics.getElem_last_of_getLast? hp.2.2 (by omega)
  rw [← hlast, PathBasics.path_adj_iff hp.1 hk (by omega)]
  have heq : (p[k]'hk = p[p.length - 2]'(by omega)) ↔ k = p.length - 2 :=
    hp.1.2.1.getElem_inj_iff
  rw [heq]
  omega

/-- Every initial segment of a right-sequence is a right-sequence. -/
theorem rightSequence_take {G : SimpleGraph V} {A C B : Set V} {x : List V}
    (hx : IsRightSequence G A C B x) (n : ℕ) :
    IsRightSequence G A C B (x.take n) := by
  obtain ⟨⟨hnd, hB⟩, h2, h3⟩ := hx
  refine ⟨⟨hnd.take, ?_⟩, ?_, ?_⟩
  · intro v hv
    exact hB v (List.mem_of_mem_take hv)
  · intro i hi hcomp
    have hix : i < x.length := by
      rw [List.length_take] at hi
      omega
    have hget : (x.take n)[i]'hi = x[i]'hix := List.getElem_take
    rw [hget] at hcomp ⊢
    obtain ⟨y, hy, hny⟩ := h2 i hix hcomp
    refine ⟨y, ?_, hny⟩
    have hin : i ≤ n := by
      rw [List.length_take] at hi
      omega
    rw [List.take_take, min_eq_left hin]
    exact hy
  · intro i hi hanti
    have hix : i < x.length := by
      rw [List.length_take] at hi
      omega
    have hget : (x.take n)[i]'hi = x[i]'hix := List.getElem_take
    rw [hget] at hanti ⊢
    obtain ⟨r, R, hban, y, hy, hny⟩ := h3 i hix hanti
    refine ⟨r, R, hban, y, ?_, hny⟩
    have hin : i ≤ n := by
      rw [List.length_take] at hi
      omega
    rw [List.take_take, min_eq_left hin]
    exact hy

/-- Every `B`-complete vertex lies outside the strip of a step-connected strip. -/
theorem bComplete_not_mem_strip {G : SimpleGraph V} {A C B : Set V}
    (hS : StepConnected G A C B) {v : V} (hv : VertexComplete G v B) :
    v ∉ A ∪ B ∪ C := by
  obtain ⟨⟨hAB, _, _⟩, ⟨_, _⟩, _, hstep, _⟩ := hS
  intro hmem
  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstp, hvin⟩ := hstep v hmem
  obtain ⟨hr1, hr2, -, hcross⟩ := hstp
  have hb₁ : b₁ ∈ R₁ := PathBasics.getLast_mem hr1.1.2.2
  have hb₂ : b₂ ∈ R₂ := PathBasics.getLast_mem hr2.1.2.2
  rcases hvin with hv1 | hv2
  · have hadj : G.Adj v b₂ := hv b₂ hr2.2.2.1
    rcases (hcross v hv1 b₂ hb₂).mp hadj with ⟨-, hba⟩ | ⟨hvb, -⟩
    · exact (Set.disjoint_left.mp hAB hr2.2.1) (hba ▸ hr2.2.2.1)
    · exact G.irrefl (hvb ▸ hv v (hvb ▸ hr1.2.2.1))
  · have hadj : G.Adj b₁ v := (hv b₁ hr1.2.2.1).symm
    rcases (hcross b₁ hb₁ v hv2).mp hadj with ⟨hba, -⟩ | ⟨-, hvb⟩
    · exact (Set.disjoint_left.mp hAB hr1.2.1) (hba ▸ hr1.2.2.1)
    · exact G.irrefl (hvb ▸ hv v (hvb ▸ hr2.2.2.1))

/-- A `B`-complete vertex different from the right end of a staircase lies
outside the whole staircase. -/
theorem bComplete_not_mem_staircase {G : SimpleGraph V} {A C B : Set V}
    {a₀ b₀ v : V} {R₀ : List V} (hK : IsStaircase G A C B a₀ R₀ b₀)
    (hvB : VertexComplete G v B) (hvb : v ≠ b₀) :
    v ∉ staircaseVertices A C B R₀ := by
  obtain ⟨hS, hban, -⟩ := hK
  obtain ⟨b, hbB⟩ := hS.2.1.2
  rintro (hvR | hvS)
  · by_cases hva : v = a₀
    · exact hban.2.2.1.2.2 b (Or.inl hbB) (hva ▸ hvB b hbB)
    · have hvint : v ∈ interior R₀ :=
        (PathBasics.mem_interior_iff_of_pathFrom hban.1).mpr ⟨hvR, hva, hvb⟩
      exact hban.2.2.2.2 v hvint b (Or.inl (Or.inr hbB)) (hvB b hbB)
  · exact bComplete_not_mem_strip hS hvB hvS

/-- A `B`-complete vertex adjacent to the left end is outside the staircase
(in particular it cannot be the right end). -/
theorem bComplete_adj_left_not_mem_staircase {G : SimpleGraph V} {A C B : Set V}
    {a₀ b₀ v : V} {R₀ : List V} (hK : IsStaircase G A C B a₀ R₀ b₀)
    (hvB : VertexComplete G v B) (hva : G.Adj v a₀) :
    v ∉ staircaseVertices A C B R₀ := by
  apply bComplete_not_mem_staircase hK hvB
  rintro rfl
  have hlen : 3 ≤ R₀.length := by
    have hpl := hK.2.2
    have heq := PathBasics.pathLength_eq R₀
    omega
  have hpos : 0 < R₀.length := by omega
  have hn := PathBasics.path_ends_not_adj hK.2.1.1.1 hlen
  have h0 : R₀[0]'hpos = a₀ :=
    PathBasics.getElem_zero_of_head? hK.2.1.1.2.1 hpos
  have hl : R₀[R₀.length - 1]'(by omega) = v :=
    PathBasics.getElem_last_of_getLast? hK.2.1.1.2.2 hpos
  apply hn
  simpa [h0, hl] using hva.symm

/-- A major vertex cannot be minor. -/
theorem not_minor_of_major {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ v : V}
    {R₀ : List V} (hK : IsStaircase G A C B a₀ R₀ b₀)
    (hmaj : MajorForStaircase G A C B a₀ R₀ b₀ v) :
    ¬ MinorForStaircase G A C B a₀ R₀ b₀ v := by
  obtain ⟨hS, hban, -⟩ := hK
  obtain ⟨-, ⟨a, ha, hva⟩, ⟨b, hb, hvb⟩, ⟨r, hr, hvr⟩⟩ := hmaj
  rintro ⟨-, hloc⟩
  have hma : a ∈ G.neighborSet v ∩ staircaseVertices A C B R₀ :=
    ⟨hva, Or.inr (Or.inl (Or.inl ha))⟩
  have hmb : b ∈ G.neighborSet v ∩ staircaseVertices A C B R₀ :=
    ⟨hvb, Or.inr (Or.inl (Or.inr hb))⟩
  have hmr : r ∈ G.neighborSet v ∩ staircaseVertices A C B R₀ := ⟨hvr, Or.inl hr⟩
  rcases hloc with h | h | h | h
  · exact hban.2.1 r hr (h hmr)
  · exact hban.2.1 a (h hma) (Or.inl (Or.inl ha))
  · rcases h hmb with hbA | hba
    · exact (Set.disjoint_left.mp hS.1.1 hbA) hb
    · exact hban.2.2.1.1 (Or.inl (Or.inr ((Set.mem_singleton_iff.mp hba) ▸ hb)))
  · rcases h hma with haB | hab
    · exact (Set.disjoint_left.mp hS.1.1 ha) haB
    · exact hban.2.2.2.1.1 (Or.inl (Or.inl ((Set.mem_singleton_iff.mp hab) ▸ ha)))

/-- A major vertex falls into the middle alternative of 12.1. -/
theorem major_diagonal_or_central {G : SimpleGraph V} (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G s t R₁ R₂ R₃)
    (h1br : ¬ ∃ A' C' B' F Q : Set V, IsOneBreaker G A' C' B' F Q)
    {A C B : Set V} {a₀ b₀ v : V} {R₀ : List V}
    (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    (hv : v ∉ staircaseVertices A C B R₀)
    (hmaj : MajorForStaircase G A C B a₀ R₀ b₀ v) :
    LeftDiagonal G A C B a₀ R₀ b₀ v ∨
      RightDiagonal G A C B a₀ R₀ b₀ v ∨
      CentralForStaircase G A C B a₀ R₀ b₀ v := by
  obtain ⟨i, hi, -⟩ :=
    Workspace.Statements.S12.SPGT.thm_12_1 G hG hK4 heven h1br A C B a₀ b₀ R₀ hK v hv
  fin_cases i
  · simp only [Matrix.cons_val_zero] at hi
    exact absurd hi.1 (not_minor_of_major hK.1 hmaj)
  · simpa only [Matrix.cons_val_one, Matrix.head_cons] using hi.2
  · simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hi
    rcases hi with ⟨hls, -⟩ | ⟨hrs, -⟩
    · obtain ⟨b, hb, hvb⟩ := hmaj.2.2.1
      exact absurd hvb (hls.2.2 b (Or.inl hb))
    · obtain ⟨a, ha, hva⟩ := hmaj.2.1
      exact absurd hva (hrs.2.2 a (Or.inl ha))

/-- Classification of a `B`-complete vertex outside the staircase: it is a
right-star or major. -/
theorem bComplete_rightStar_or_major {G : SimpleGraph V} (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G s t R₁ R₂ R₃)
    (h1br : ¬ ∃ A' C' B' F Q : Set V, IsOneBreaker G A' C' B' F Q)
    {A C B : Set V} {a₀ b₀ v : V} {R₀ : List V}
    (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    (hv : v ∉ staircaseVertices A C B R₀)
    (hvB : VertexComplete G v B) :
    IsRightStar G A C B v ∨ MajorForStaircase G A C B a₀ R₀ b₀ v := by
  obtain ⟨i, hi, -⟩ :=
    Workspace.Statements.S12.SPGT.thm_12_1 G hG hK4 heven h1br A C B a₀ b₀ R₀ hK v hv
  fin_cases i
  · simp only [Matrix.cons_val_zero] at hi
    exact Or.inl (hi.2.2.resolve_right (fun h => h hvB))
  · simp only [Matrix.cons_val_one, Matrix.head_cons] at hi
    exact Or.inr hi.1
  · simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hi
    rcases hi with ⟨hls, -⟩ | ⟨hrs, -⟩
    · obtain ⟨b, hb⟩ := hK.1.1.2.1.2
      exact absurd (hvB b hb) (hls.2.2 b (Or.inl hb))
    · exact Or.inl hrs

/-- The chain of predecessors starting at `x[i]`, stopped at the first term
failing a predicate `LD`.  It is an antipath because each predecessor is the
earliest nonneighbour. -/
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
    · have hcomp : VertexComplete G (x[i]'hi) A := hLD _ hLDi
      obtain ⟨y, hy, hny⟩ := hx.2.1 i hi hcomp
      have hQ : ∃ k : ℕ, ∃ hk : k < x.length, k < i ∧ ¬ G.Adj (x[k]'hk) (x[i]'hi) := by
        obtain ⟨k, hk, hkval⟩ := List.mem_iff_getElem.mp hy
        have hklen : k < (x.take i).length := hk
        rw [List.length_take] at hklen
        have hkx : k < x.length := by omega
        have hki : k < i := by omega
        refine ⟨k, hkx, hki, ?_⟩
        have he : (x.take i)[k]'hk = x[k]'hkx := List.getElem_take
        rw [he] at hkval
        rw [hkval]
        exact hny
      set Q : ℕ → Prop := fun k => ∃ hk : k < x.length, k < i ∧
        ¬ G.Adj (x[k]'hk) (x[i]'hi)
      have hQex : ∃ k, Q k := hQ
      obtain ⟨hhx, hhi, hhadj⟩ := Nat.find_spec hQex
      set h := Nat.find hQex
      have hmin : ∀ k : ℕ, k < h → ∀ hk : k < x.length,
          G.Adj (x[k]'hk) (x[i]'hi) := by
        intro k hkh hk
        have hn := Nat.find_min hQex hkh
        by_contra hc
        exact hn ⟨hk, by omega, hc⟩
      obtain ⟨L', j, hj, hL', hidx', hLD', hnLD'⟩ := IH h hhi hhx
      have hidxlt : ∀ w ∈ L', w ≠ x[h]'hhx →
          ∃ (k : ℕ) (hk : k < x.length), k < h ∧ x[k]'hk = w := by
        intro w hw hwne
        obtain ⟨k, hk, hkh, hkw⟩ := hidx' w hw
        refine ⟨k, hk, ?_, hkw⟩
        rcases lt_or_eq_of_le hkh with h1 | h1
        · exact h1
        · exfalso
          apply hwne
          subst h1
          simpa using hkw.symm
      have hxinotL' : (x[i]'hi) ∉ L' := by
        intro hmem
        obtain ⟨k, hk, hkh, hkw⟩ := hidx' _ hmem
        have hne : k ≠ i := by omega
        exact hne ((List.Nodup.getElem_inj_iff hx.1.1).mp hkw)
      have hcons : ∀ y ∈ L', (Gᶜ.Adj (x[i]'hi) y ↔ y = x[h]'hhx) := by
        intro z hz
        constructor
        · intro hadj
          by_contra hzne
          obtain ⟨k, hk, hkh, hkw⟩ := hidxlt z hz hzne
          have ha := hmin k hkh hk
          rw [hkw] at ha
          exact ((SimpleGraph.compl_adj G _ _).mp hadj).2 ha.symm
        · intro hzh
          subst hzh
          exact (SimpleGraph.compl_adj G _ _).mpr
            ⟨fun hc => by
              have : i = h := (List.Nodup.getElem_inj_iff hx.1.1).mp hc
              omega,
             fun hc => hhadj hc.symm⟩
      have hpath : IsPathFrom Gᶜ ((x[i]'hi) :: L') (x[i]'hi) (x[j]'hj) :=
        isPathFrom_cons hL' hxinotL' hcons
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
        by intro w hw; simp only [List.mem_singleton] at hw;
           exact ⟨i, hi, le_rfl, hw.symm⟩,
        by intro w hw hwne; simp only [List.mem_singleton] at hw; exact absurd hw hwne,
        hLDi⟩

/-- Every term of a right-sequence has the trajectory specified in the
definition of §13.  At each recursive step we choose the earliest earlier
nonneighbour, i.e. the predecessor. -/
theorem exists_trajectoryOfIndex {G : SimpleGraph V} {A C B : Set V} {x : List V}
    (hx : IsRightSequence G A C B x) :
    ∀ (i : ℕ) (hi : i < x.length),
      ∃ (w : List V) (j : ℕ) (hj : j < x.length),
        trajectoryOfIndex G A x i w ∧
        IsAntipathFrom G w (x[i]'hi) (x[j]'hj) ∧
        ∀ z ∈ w, ∃ (k : ℕ) (hk : k < x.length), k ≤ i ∧ x[k]'hk = z := by
  classical
  intro i
  induction i using Nat.strong_induction_on with
  | _ i IH =>
    intro hi
    by_cases hcomp : VertexComplete G (x[i]'hi) A
    · obtain ⟨y, hy, hny⟩ := hx.2.1 i hi hcomp
      have hex : ∃ k : ℕ, ∃ hk : k < x.length, k < i ∧
          ¬ G.Adj (x[k]'hk) (x[i]'hi) := by
        obtain ⟨k, hk, hky⟩ := List.mem_iff_getElem.mp hy
        have hklen : k < (x.take i).length := hk
        rw [List.length_take] at hklen
        have hkx : k < x.length := by omega
        have hki : k < i := by omega
        refine ⟨k, hkx, hki, ?_⟩
        have he : (x.take i)[k]'hk = x[k]'hkx := List.getElem_take
        rw [he] at hky
        simpa [hky] using hny
      set Q : ℕ → Prop := fun k => ∃ hk : k < x.length, k < i ∧
        ¬ G.Adj (x[k]'hk) (x[i]'hi)
      have hQ : ∃ k, Q k := hex
      obtain ⟨hhx, hhi, hnon⟩ := Nat.find_spec hQ
      set h := Nat.find hQ
      have hmin : ∀ k : ℕ, k < h → ∀ hk : k < x.length,
          G.Adj (x[k]'hk) (x[i]'hi) := by
        intro k hkh hk
        have hn := Nat.find_min hQ hkh
        by_contra hc
        exact hn ⟨hk, by omega, hc⟩
      obtain ⟨w, j, hj, hw, hwpath, hwidx⟩ := IH h hhi hhx
      have hwone : 1 ≤ w.length := hw.1.1
      have hwpos : 0 < w.length := by omega
      have hwhead : w[0]'hwpos = x[h]'hhx := by
        have hsome : x[h]? = some (x[h]'hhx) := List.getElem?_eq_getElem hhx
        have hhead := hw.1.2
        rw [hsome] at hhead
        exact PathBasics.getElem_zero_of_head? hhead hwpos
      have hidxlt : ∀ z ∈ w, z ≠ x[h]'hhx →
          ∃ (k : ℕ) (hk : k < x.length), k < h ∧ x[k]'hk = z := by
        intro z hz hzne
        obtain ⟨k, hk, hkh, hkz⟩ := hwidx z hz
        refine ⟨k, hk, ?_, hkz⟩
        rcases lt_or_eq_of_le hkh with hlt | heq
        · exact hlt
        · exfalso
          apply hzne
          subst heq
          simpa using hkz.symm
      have hxinot : (x[i]'hi) ∉ w := by
        intro hmem
        obtain ⟨k, hk, hkh, hkz⟩ := hwidx _ hmem
        have hki : k ≠ i := by omega
        exact hki ((List.Nodup.getElem_inj_iff hx.1.1).mp hkz)
      have hcons : ∀ z ∈ w, (Gᶜ.Adj (x[i]'hi) z ↔ z = x[h]'hhx) := by
        intro z hz
        constructor
        · intro hadj
          by_contra hzne
          obtain ⟨k, hk, hkh, hkz⟩ := hidxlt z hz hzne
          have ha := hmin k hkh hk
          rw [hkz] at ha
          exact ((SimpleGraph.compl_adj G _ _).mp hadj).2 ha.symm
        · intro hzeq
          subst hzeq
          exact (SimpleGraph.compl_adj G _ _).mpr
            ⟨fun hc => by
              have : i = h := (List.Nodup.getElem_inj_iff hx.1.1).mp hc
              omega,
             fun hc => hnon hc.symm⟩
      have hnewpath : IsAntipathFrom G ((x[i]'hi) :: w) (x[i]'hi) (x[j]'hj) :=
        isPathFrom_cons hwpath hxinot hcons
      refine ⟨(x[i]'hi) :: w, j, hj, ?_, hnewpath, ?_⟩
      · refine ⟨⟨by simp, by simp⟩, ?_, ?_⟩
        · obtain ⟨u, hu, a, ha, hnua⟩ := hw.2.1
          refine ⟨u, ?_, a, ha, hnua⟩
          rw [List.getLast?_cons_of_ne_nil (List.ne_nil_of_length_pos hwpos)]
          exact hu
        · intro j hj
          cases j with
          | zero =>
              refine ⟨hcomp, ?_⟩
              refine ⟨i, hi, rfl, h, hhi, ?_, hnon, ?_⟩
              · exact hwhead.symm
              · intro k hk
                exact hmin k hk (by omega)
          | succ j =>
              have hj' : j + 1 < w.length := by simpa using hj
              simpa using hw.2.2 j hj'
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨i, hi, le_rfl, rfl⟩
        · obtain ⟨k, hk, hkh, hkz⟩ := hwidx z hz
          exact ⟨k, hk, by omega, hkz⟩
    · have hnon : ∃ a ∈ A, ¬ G.Adj (x[i]'hi) a := by
        rw [VertexComplete] at hcomp
        push_neg at hcomp
        exact hcomp
      refine ⟨[x[i]'hi], i, hi, ?_,
        ⟨PathBasics.isPathList_singleton Gᶜ _, by simp, by simp⟩, ?_⟩
      · refine ⟨⟨by simp, by simp⟩, ⟨x[i]'hi, by simp, hnon⟩, ?_⟩
        intro j hj
        simp at hj
      · intro z hz
        simp only [List.mem_singleton] at hz
        exact ⟨i, hi, le_rfl, hz.symm⟩

/-- A left-star which is not complete to the terms of a right-sequence has a
trajectory in the sense of `trajectoryOfVertex`. -/
theorem exists_trajectoryOfVertex_of_leftStar
    {G : SimpleGraph V} {A C B : Set V} {x : List V} {a : V}
    (hS : StepConnected G A C B) (hx : IsRightSequence G A C B x)
    (ha : IsLeftStar G A C B a)
    (hanc : ¬ VertexComplete G a {v : V | v ∈ x}) :
    ∃ (w : List V) (i : ℕ) (hi : i < x.length) (j : ℕ) (hj : j < x.length),
      trajectoryOfVertex G A x a (a :: w) ∧
      birth G A C B x a x[i] ∧
      IsAntipathFrom G (a :: w) a (x[j]'hj) ∧
      (∀ z ∈ w, ∃ (k : ℕ) (hk : k < x.length), k ≤ i ∧ x[k]'hk = z) := by
  classical
  have hax : a ∉ x := by
    intro hmem
    obtain ⟨b, hb⟩ := hS.2.1.2
    have haB := hx.1.2 a hmem b hb
    exact ha.2.2 b (Or.inl hb) haB
  have hex : ∃ i : ℕ, ∃ hi : i < x.length, ¬ G.Adj a (x[i]'hi) := by
    rw [VertexComplete] at hanc
    push_neg at hanc
    obtain ⟨v, hv, hnav⟩ := hanc
    obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.mp hv
    exact ⟨i, hi, by simpa [hiv] using hnav⟩
  set Q : ℕ → Prop := fun i => ∃ hi : i < x.length, ¬ G.Adj a (x[i]'hi)
  have hQ : ∃ i, Q i := hex
  obtain ⟨hi, hani⟩ := Nat.find_spec hQ
  set i := Nat.find hQ
  have hmin : ∀ k : ℕ, k < i → ∀ hk : k < x.length, G.Adj a (x[k]'hk) := by
    intro k hki hk
    have hn := Nat.find_min hQ hki
    by_contra hc
    exact hn ⟨hk, hc⟩
  obtain ⟨w, j, hj, hw, hwpath, hwidx⟩ := exists_trajectoryOfIndex hx i hi
  have hwhead_mem : x[i]'hi ∈ w := PathBasics.head_mem hwpath.2.1
  have hanotw : a ∉ w := by
    intro haw
    obtain ⟨k, hk, -, hkz⟩ := hwidx a haw
    exact hax (hkz ▸ List.getElem_mem hk)
  have hcons : ∀ z ∈ w, (Gᶜ.Adj a z ↔ z = x[i]'hi) := by
    intro z hz
    constructor
    · intro hadj
      by_contra hzne
      obtain ⟨k, hk, hki, hkz⟩ := hwidx z hz
      have hki' : k < i := by
        rcases lt_or_eq_of_le hki with h | h
        · exact h
        · exfalso
          apply hzne
          subst h
          simpa using hkz.symm
      have haadj := hmin k hki' hk
      rw [hkz] at haadj
      exact ((SimpleGraph.compl_adj G _ _).mp hadj).2 haadj
    · rintro rfl
      exact (SimpleGraph.compl_adj G _ _).mpr
        ⟨fun heq => hax (heq ▸ List.getElem_mem hi), hani⟩
  have hapath : IsAntipathFrom G (a :: w) a (x[j]'hj) :=
    isPathFrom_cons hwpath hanotw hcons
  have hbirth : birth G A C B x a x[i] := by
    refine ⟨ha, hanc, i, hi, rfl, hani, ?_⟩
    intro k hk
    exact hmin k hk (by omega)
  refine ⟨w, i, hi, j, hj, ?_, hbirth, hapath, hwidx⟩
  refine ⟨⟨ha.2.1, hax, hanc⟩, i, hi, w, ?_, hw, rfl⟩
  refine ⟨hani, ?_⟩
  intro k hk
  exact hmin k hk (by omega)

end Workspace.ProofLemmas.Thm132Infrastructure
