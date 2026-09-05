import Workspace.ProofLemmas.Thm93KnotModel
import Workspace.ProofLemmas.SubdivisionCounting

/-!
# The host graph of the canonical knot appearance

PAPER (9.3, printed p. 48): *"For assume `Q₁, Q₂` have length 1.  Then `K` is a degenerate
appearance of `K₄` in `G`, say `K = L(H)`."*

`Workspace.ProofLemmas.Thm93KnotModel.graph m n` is the induced subgraph `K` of a knot whose
two antipaths have length one, written down explicitly in terms of the numbers of vertices
`m, n` of its two paths.  This file builds the subdivision `H` of `K₄` with `L(H) = K`.

`H` is a four-cycle `c₁c₂c₃c₄` in which the two opposite pairs `c₁c₃` and `c₂c₄` are joined by
extra tracks with `m` and `n` edges.  Its vertices are therefore two chains: `Fin (m+1)` for
the `c₁c₃` track (with `c₁` at `0` and `c₃` at `m`) and `Fin (n+1)` for the `c₂c₄` track (with
`c₂` at `0` and `c₄` at `n`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm93KnotHost

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm93KnotModel

/-- The vertices of the host graph: the `c₁c₃` chain and the `c₂c₄` chain. -/
abbrev Host (m n : ℕ) := Fin (m + 1) ⊕ Fin (n + 1)

/-- Adjacency of the host graph: consecutive vertices along each chain, plus the four edges
joining an end of one chain to an end of the other. -/
def HostAdj (m n : ℕ) : Host m n → Host m n → Prop
  | .inl i, .inl j => i.val + 1 = j.val ∨ j.val + 1 = i.val
  | .inr i, .inr j => i.val + 1 = j.val ∨ j.val + 1 = i.val
  | .inl i, .inr j => (i.val = 0 ∨ i.val = m) ∧ (j.val = 0 ∨ j.val = n)
  | .inr j, .inl i => (i.val = 0 ∨ i.val = m) ∧ (j.val = 0 ∨ j.val = n)

/-- The host graph. -/
def host (m n : ℕ) : SimpleGraph (Host m n) where
  Adj := HostAdj m n
  symm := by rintro (i | i) (j | j) h <;> dsimp [HostAdj] at h ⊢ <;> omega
  loopless := by
    refine ⟨?_⟩
    rintro (i | i) <;> dsimp [HostAdj] <;> omega

@[simp] theorem host_adj_ll {m n : ℕ} (i j : Fin (m + 1)) :
    (host m n).Adj (.inl i) (.inl j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := Iff.rfl

@[simp] theorem host_adj_rr {m n : ℕ} (i j : Fin (n + 1)) :
    (host m n).Adj (.inr i) (.inr j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := Iff.rfl

@[simp] theorem host_adj_lr {m n : ℕ} (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (host m n).Adj (.inl i) (.inr j) ↔ (i.val = 0 ∨ i.val = m) ∧ (j.val = 0 ∨ j.val = n) :=
  Iff.rfl

@[simp] theorem host_adj_rl {m n : ℕ} (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (host m n).Adj (.inr j) (.inl i) ↔ (i.val = 0 ∨ i.val = m) ∧ (j.val = 0 ∨ j.val = n) :=
  Iff.rfl

/-- The four branch-vertices, in cyclic order along the degenerate four-cycle. -/
def c1 (m n : ℕ) : Host m n := .inl 0
/-- The second branch-vertex. -/
def c2 (m n : ℕ) : Host m n := .inr 0
/-- The third branch-vertex. -/
def c3 (m n : ℕ) : Host m n := .inl (Fin.last m)
/-- The fourth branch-vertex. -/
def c4 (m n : ℕ) : Host m n := .inr (Fin.last n)

/-- The chain carrying the first path of the knot. -/
def chainA (m n : ℕ) : List (Host m n) := List.ofFn (Sum.inl : Fin (m + 1) → Host m n)
/-- The chain carrying the second path of the knot. -/
def chainB (m n : ℕ) : List (Host m n) := List.ofFn (Sum.inr : Fin (n + 1) → Host m n)


/-- The edge of the host graph corresponding to a vertex of `graph m n`.
The `i`-th vertex of the first path is the `i`-th edge of the `c₁c₃` chain, the `j`-th vertex
of the second path is the `j`-th edge of the `c₂c₄` chain, and the four antipath vertices
`x₁, x₂, y₁, y₂` are the four edges `c₁c₂`, `c₄c₁`, `c₃c₄`, `c₂c₃` of the four-cycle. -/
def edgeOf (m n : ℕ) : Vertex m n → Sym2 (Host m n)
  | .inl i => s(.inl i.castSucc, .inl i.succ)
  | .inr (.inl j) => s(.inr j.castSucc, .inr j.succ)
  | .inr (.inr k) =>
      ![s(c1 m n, c2 m n), s(c1 m n, c4 m n), s(c3 m n, c4 m n), s(c3 m n, c2 m n)] k

/-- Two edges of a graph meet exactly when they share an end. -/
theorem sym2_meet {α : Type*} (x y z t : α) :
    (∃ w, w ∈ s(x, y) ∧ w ∈ s(z, t)) ↔ (x = z ∨ x = t ∨ y = z ∨ y = t) := by
  constructor
  · rintro ⟨w, hw1, hw2⟩
    rw [Sym2.mem_iff] at hw1 hw2
    rcases hw1 with rfl | rfl <;> rcases hw2 with h | h <;> subst h <;> tauto
  · rintro (h | h | h | h)
    exacts [⟨x, by simp, by simp [h]⟩, ⟨x, by simp, by simp [h]⟩,
      ⟨y, by simp, by simp [h]⟩, ⟨y, by simp, by simp [h]⟩]

theorem edgeOf_mem_edgeSet {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (u : Vertex m n) :
    edgeOf m n u ∈ (host m n).edgeSet := by
  rcases u with i | j | k
  · simp [edgeOf, SimpleGraph.mem_edgeSet, Fin.val_succ]
  · simp [edgeOf, SimpleGraph.mem_edgeSet, Fin.val_succ]
  · fin_cases k <;>
      simp [edgeOf, SimpleGraph.mem_edgeSet, c1, c2, c3, c4, Fin.val_last]

theorem edgeOf_injective {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    Function.Injective (edgeOf m n) := by
  have hml : ((Fin.last m : Fin (m + 1)) : ℕ) = m := rfl
  have hnl : ((Fin.last n : Fin (n + 1)) : ℕ) = n := rfl
  rintro (i | j | k) (i' | j' | k') h <;>
    simp only [edgeOf, c1, c2, c3, c4, Sym2.eq_iff, Prod.mk.injEq,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and, and_false, or_false, false_or,
      Fin.ext_iff, Fin.val_succ, Fin.val_castSucc, hml, hnl, Fin.val_zero] at h ⊢ <;>
    first
      | omega
      | (fin_cases k <;> fin_cases k' <;>
          simp_all [Fin.ext_iff] <;> omega)
      | (fin_cases k <;> simp_all [Fin.ext_iff] <;> omega)
      | (fin_cases k' <;> simp_all [Fin.ext_iff] <;> omega)


theorem edgeOf_surjective {m n : ℕ} (e : Sym2 (Host m n)) (he : e ∈ (host m n).edgeSet) :
    ∃ u, edgeOf m n u = e := by
  induction e using Sym2.ind with
  | _ a b =>
  rw [SimpleGraph.mem_edgeSet] at he
  rcases a with i | i <;> rcases b with j | j
  · rw [host_adj_ll] at he
    have hi := i.isLt
    have hj := j.isLt
    rcases he with h | h
    · exact ⟨Sum.inl ⟨i.val, by omega⟩, by
        simp only [edgeOf, Sym2.eq_iff, Sum.inl.injEq, Fin.ext_iff, Fin.val_castSucc,
          Fin.val_succ, true_and]; omega⟩
    · exact ⟨Sum.inl ⟨j.val, by omega⟩, by
        simp only [edgeOf, Sym2.eq_iff, Sum.inl.injEq, Fin.ext_iff, Fin.val_castSucc,
          Fin.val_succ, true_and]; omega⟩
  · rw [host_adj_lr] at he
    obtain ⟨hi | hi, hj | hj⟩ := he
    · exact ⟨cross 0, by
        simp only [edgeOf, cross, c1, c2, Matrix.cons_val_zero, Sym2.eq_iff, Sum.inl.injEq,
          Sum.inr.injEq, Fin.ext_iff, Fin.val_zero, reduceCtorEq, and_false, or_false]
        omega⟩
    · exact ⟨cross 1, by
        simp only [edgeOf, cross, c1, c4, Matrix.cons_val_one, Matrix.cons_val_zero,
          Matrix.head_cons, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, Fin.ext_iff,
          Fin.val_zero, Fin.val_last, reduceCtorEq, and_false, or_false]
        omega⟩
    · exact ⟨cross 3, by
        simp only [edgeOf, cross, c3, c2, Sym2.eq_iff, Sum.inl.injEq,
          Sum.inr.injEq, Fin.ext_iff, Fin.val_zero, Fin.val_last, reduceCtorEq, and_false,
          or_false, Matrix.cons_val_three, Matrix.head_cons, Matrix.cons_val_one,
          Matrix.tail_cons, Matrix.cons_val_zero]
        omega⟩
    · exact ⟨cross 2, by
        simp only [edgeOf, cross, c3, c4, Sym2.eq_iff, Sum.inl.injEq,
          Sum.inr.injEq, Fin.ext_iff, Fin.val_last, reduceCtorEq, and_false,
          or_false, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
          Matrix.cons_val_one, Matrix.cons_val_zero]
        omega⟩
  · rw [host_adj_rl] at he
    obtain ⟨hj | hj, hi | hi⟩ := he
    · refine ⟨cross 0, ?_⟩
      rw [Sym2.eq_swap]
      simp only [edgeOf, cross, c1, c2, Matrix.cons_val_zero, Sym2.eq_iff, Sum.inl.injEq,
        Sum.inr.injEq, Fin.ext_iff, Fin.val_zero, reduceCtorEq, and_false, or_false]
      omega
    · refine ⟨cross 1, ?_⟩
      rw [Sym2.eq_swap]
      simp only [edgeOf, cross, c1, c4, Matrix.cons_val_one, Matrix.cons_val_zero,
        Matrix.head_cons, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, Fin.ext_iff,
        Fin.val_zero, Fin.val_last, reduceCtorEq, and_false, or_false]
      omega
    · refine ⟨cross 3, ?_⟩
      rw [Sym2.eq_swap]
      simp only [edgeOf, cross, c3, c2, Sym2.eq_iff, Sum.inl.injEq,
        Sum.inr.injEq, Fin.ext_iff, Fin.val_zero, Fin.val_last, reduceCtorEq, and_false,
        or_false, Matrix.cons_val_three, Matrix.head_cons, Matrix.cons_val_one,
        Matrix.tail_cons, Matrix.cons_val_zero]
      omega
    · refine ⟨cross 2, ?_⟩
      rw [Sym2.eq_swap]
      simp only [edgeOf, cross, c3, c4, Sym2.eq_iff, Sum.inl.injEq,
        Sum.inr.injEq, Fin.ext_iff, Fin.val_last, reduceCtorEq, and_false,
        or_false, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        Matrix.cons_val_one, Matrix.cons_val_zero]
      omega
  · rw [host_adj_rr] at he
    have hi := i.isLt
    have hj := j.isLt
    rcases he with h | h
    · exact ⟨Sum.inr (Sum.inl ⟨i.val, by omega⟩), by
        simp only [edgeOf, Sym2.eq_iff, Sum.inr.injEq, Fin.ext_iff, Fin.val_castSucc,
          Fin.val_succ, true_and]; omega⟩
    · exact ⟨Sum.inr (Sum.inl ⟨j.val, by omega⟩), by
        simp only [edgeOf, Sym2.eq_iff, Sum.inr.injEq, Fin.ext_iff, Fin.val_castSucc,
          Fin.val_succ, true_and]; omega⟩


theorem meet_comm {α : Type*} (e f : Sym2 α) :
    (∃ w, w ∈ e ∧ w ∈ f) ↔ (∃ w, w ∈ f ∧ w ∈ e) := by
  constructor <;> rintro ⟨w, h1, h2⟩ <;> exact ⟨w, h2, h1⟩

theorem meet_inl_cross {m n : ℕ} (hm : 2 ≤ m) (i : Fin m) (k : Fin 4) :
    (∃ w, w ∈ edgeOf m n (Sum.inl i) ∧ w ∈ edgeOf m n (cross k)) ↔
      ((i : ℕ) = 0 ∧ (k : ℕ) < 2) ∨ ((i : ℕ) + 1 = m ∧ 2 ≤ (k : ℕ)) := by
  have hi := i.isLt
  fin_cases k <;>
    simp [edgeOf, cross, c1, c2, c3, c4, sym2_meet, Fin.ext_iff] <;> omega

theorem meet_inr_cross {m n : ℕ} (hn : 2 ≤ n) (j : Fin n) (k : Fin 4) :
    (∃ w, w ∈ edgeOf m n (Sum.inr (Sum.inl j)) ∧ w ∈ edgeOf m n (cross k)) ↔
      ((j : ℕ) = 0 ∧ ((k : ℕ) = 0 ∨ (k : ℕ) = 3)) ∨
        ((j : ℕ) + 1 = n ∧ ((k : ℕ) = 1 ∨ (k : ℕ) = 2)) := by
  have hj := j.isLt
  fin_cases k <;>
    simp [edgeOf, cross, c1, c2, c3, c4, sym2_meet, Fin.ext_iff] <;> omega

theorem meet_cross_cross {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (k k' : Fin 4) (hk : k ≠ k') :
    (∃ w, w ∈ edgeOf m n (cross k) ∧ w ∈ edgeOf m n (cross k')) ↔
      (k : ℕ) % 2 ≠ (k' : ℕ) % 2 := by
  fin_cases k <;> fin_cases k' <;>
    simp_all [edgeOf, cross, c1, c2, c3, c4, sym2_meet, Fin.ext_iff] <;> omega

theorem graph_adj_def (m n : ℕ) (u v : Vertex m n) :
    (graph m n).Adj u v ↔ Adj m n u v := Iff.rfl

/-- Two vertices of `graph m n` are adjacent exactly when the corresponding two edges of the
host graph are distinct and share an end. -/
theorem edgeOf_meet_iff {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (u v : Vertex m n) :
    (u ≠ v ∧ ∃ w, w ∈ edgeOf m n u ∧ w ∈ edgeOf m n v) ↔ (graph m n).Adj u v := by
  rw [graph_adj_def]
  rcases u with i | j | k <;> rcases v with i' | j' | k'
  · have hi := i.isLt
    have hi' := i'.isLt
    simp only [edgeOf, sym2_meet, Adj, ne_eq, Sum.inl.injEq, Fin.ext_iff, Fin.val_castSucc,
      Fin.val_succ]
    omega
  · simp only [edgeOf, sym2_meet, Adj, Sum.inl.injEq, reduceCtorEq, or_self, and_false]
  · constructor
    · rintro ⟨-, h⟩
      exact (meet_inl_cross hm i k').mp h
    · intro h
      exact ⟨by simp, (meet_inl_cross hm i k').mpr h⟩
  · simp only [edgeOf, sym2_meet, Adj, Sum.inr.injEq, reduceCtorEq, or_self, and_false]
  · have hj := j.isLt
    have hj' := j'.isLt
    simp only [edgeOf, sym2_meet, Adj, ne_eq, Sum.inr.injEq, Sum.inl.injEq, Fin.ext_iff,
      Fin.val_castSucc, Fin.val_succ]
    omega
  · constructor
    · rintro ⟨-, h⟩
      exact (meet_inr_cross hn j k').mp h
    · intro h
      exact ⟨by simp, (meet_inr_cross hn j k').mpr h⟩
  · constructor
    · rintro ⟨-, h⟩
      exact (meet_inl_cross hm i' k).mp ((meet_comm _ _).mp h)
    · intro h
      exact ⟨by simp, (meet_comm _ _).mpr ((meet_inl_cross hm i' k).mpr h)⟩
  · constructor
    · rintro ⟨-, h⟩
      exact (meet_inr_cross hn j' k).mp ((meet_comm _ _).mp h)
    · intro h
      exact ⟨by simp, (meet_comm _ _).mpr ((meet_inr_cross hn j' k).mpr h)⟩
  · constructor
    · rintro ⟨hne, h⟩
      have hk : k ≠ k' := fun hkk => hne (by rw [hkk])
      exact (meet_cross_cross hm hn k k' hk).mp h
    · intro h
      have hk : k ≠ k' := by
        intro hkk
        exact (show ¬ ((k : ℕ) % 2 ≠ (k' : ℕ) % 2) from by rw [hkk]; simp) h
      exact ⟨by simpa [Sum.inr.injEq] using hk, (meet_cross_cross hm hn k k' hk).mpr h⟩

/-! ### Degrees: the four corners of the four-cycle are the branch-vertices -/

theorem three_le_ncard_triple {α : Type*} {a b c : α} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : 3 ≤ ({a, b, c} : Set α).ncard := by
  have h1 : ({b, c} : Set α).ncard = 2 := Set.ncard_pair hbc
  have h2 : a ∉ ({b, c} : Set α) := by simp [hab, hac]
  rw [Set.ncard_insert_of_notMem h2 (Set.toFinite _), h1]

theorem ncard_le_two_of_subset {α : Type*} [Finite α] {s : Set α} {a b : α}
    (h : s ⊆ ({a, b} : Set α)) : s.ncard ≤ 2 := by
  refine le_trans (Set.ncard_le_ncard h (Set.toFinite _)) ?_
  exact le_trans (Set.ncard_insert_le _ _) (by simp)

theorem three_le_ncard_of_subset {α : Type*} [Finite α] {s : Set α} {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (h : ({a, b, c} : Set α) ⊆ s) :
    3 ≤ s.ncard :=
  le_trans (three_le_ncard_triple hab hac hbc) (Set.ncard_le_ncard h (Set.toFinite _))

theorem branchVertices_eq {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    branchVertices (host m n) = ({c1 m n, c2 m n, c3 m n, c4 m n} : Set (Host m n)) := by
  have hml : ((Fin.last m : Fin (m + 1)) : ℕ) = m := rfl
  have hnl : ((Fin.last n : Fin (n + 1)) : ℕ) = n := rfl
  ext w
  simp only [branchVertices, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    c1, c2, c3, c4]
  constructor
  · intro hw
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2, h3, h4⟩ := hcon
    have hle : ((host m n).neighborSet w).ncard ≤ 2 := by
      rcases w with i | i
      · have hi0 : i.val ≠ 0 := by
          intro h; exact h1 (congrArg Sum.inl (Fin.ext (by simpa using h)))
        have him : i.val ≠ m := by
          intro h; exact h3 (congrArg Sum.inl (Fin.ext (by simp [hml, h])))
        have hi := i.isLt
        refine ncard_le_two_of_subset (a := Sum.inl ⟨i.val - 1, by omega⟩)
          (b := Sum.inl ⟨i.val + 1, by omega⟩) ?_
        rintro (u | u) hu
        · simp only [SimpleGraph.mem_neighborSet, host_adj_ll] at hu
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sum.inl.injEq, Fin.ext_iff]
          omega
        · simp only [SimpleGraph.mem_neighborSet, host_adj_lr] at hu
          omega
      · have hi0 : i.val ≠ 0 := by
          intro h; exact h2 (congrArg Sum.inr (Fin.ext (by simpa using h)))
        have him : i.val ≠ n := by
          intro h; exact h4 (congrArg Sum.inr (Fin.ext (by simp [hnl, h])))
        have hi := i.isLt
        refine ncard_le_two_of_subset (a := Sum.inr ⟨i.val - 1, by omega⟩)
          (b := Sum.inr ⟨i.val + 1, by omega⟩) ?_
        rintro (u | u) hu
        · simp only [SimpleGraph.mem_neighborSet, host_adj_rl] at hu
          omega
        · simp only [SimpleGraph.mem_neighborSet, host_adj_rr] at hu
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sum.inr.injEq, Fin.ext_iff]
          omega
    omega
  · have key : ∀ (a b c w : Host m n), a ≠ b → a ≠ c → b ≠ c →
        (host m n).Adj w a → (host m n).Adj w b → (host m n).Adj w c →
        3 ≤ ((host m n).neighborSet w).ncard := by
      intro a b c w hab hac hbc ha hb hc
      refine three_le_ncard_of_subset hab hac hbc ?_
      rintro x hx
      rcases hx with rfl | rfl | rfl
      exacts [ha, hb, hc]
    rintro (rfl | rfl | rfl | rfl)
    · refine key (Sum.inl ⟨1, by omega⟩) (Sum.inr 0) (Sum.inr (Fin.last n)) _
        (by simp) (by simp) ?_ (by simp) (by simp [hnl]) (by simp [hnl])
      simp only [ne_eq, Sum.inr.injEq, Fin.ext_iff, Fin.val_zero, hnl]
      omega
    · refine key (Sum.inr ⟨1, by omega⟩) (Sum.inl 0) (Sum.inl (Fin.last m)) _
        (by simp) (by simp) ?_ (by simp) (by simp [hml]) (by simp [hml])
      simp only [ne_eq, Sum.inl.injEq, Fin.ext_iff, Fin.val_zero, hml]
      omega
    · refine key (Sum.inl ⟨m - 1, by omega⟩) (Sum.inr 0) (Sum.inr (Fin.last n)) _
        (by simp) (by simp) ?_ (by simp [hml]; omega) (by simp [hml, hnl]) (by simp [hml, hnl])
      simp only [ne_eq, Sum.inr.injEq, Fin.ext_iff, Fin.val_zero, hnl]
      omega
    · refine key (Sum.inr ⟨n - 1, by omega⟩) (Sum.inl 0) (Sum.inl (Fin.last m)) _
        (by simp) (by simp) ?_ (by simp [hnl]; omega) (by simp [hml, hnl]) (by simp [hml, hnl])
      simp only [ne_eq, Sum.inl.injEq, Fin.ext_iff, Fin.val_zero, hml]
      omega

end Workspace.ProofLemmas.Thm93KnotHost
