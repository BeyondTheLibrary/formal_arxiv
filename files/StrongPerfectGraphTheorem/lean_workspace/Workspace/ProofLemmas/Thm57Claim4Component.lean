import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.ProofLemmas.Thm57Claim4Config
import Workspace.ProofLemmas.Thm57Claim4Reach

/-!
# 5.7 (4): reading off the configuration `a₁b₃, b₂a₃, a₃b₃` from the component

PAPER (printed p. 24):

> *"Since there is a component of `K` containing an end of each of `x₁, x₂, x₃`, we may assume
> that `a₁b₃, b₂a₃, a₃b₃ ∈ E(K)`."*

Recall what is known about `K` at this point: its edges join an `aᵢ` to a `bⱼ` (the colour
step), and no vertex of `K` is joined to ends of *both* of the other two marked edges (the
consequence of claim (3)).  So each end has at most one neighbour outside its own marked edge,
and `K` has maximum degree two.

The lemma below extracts exactly the configuration the paper names: an index `k` whose own
marked edge is an edge of `K`, together with edges of `K` leaving `a k` and `b k` towards two
*different* other marked edges.  The proof is the paper's *"we may assume"*, made explicit.
First, no marked edge is isolated in `K`, because otherwise its two ends form a component of
`K`, and the component of `K` we are given meets all three marked edges.  With three edges and
maximum degree one at the level of marked edges, some marked edge `k` is joined to both others.
If its own edge is in `K` we are done; otherwise the path of `K` from `a k` to `b k` has to
leave and come back, and the marked edge it first reaches is the one we want.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm57Claim4Component

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm57Claim4Config
open Workspace.ProofLemmas.Thm57Claim4Reach

variable {W : Type*} [Fintype W] [DecidableEq W]

variable (H : SimpleGraph W) (X : Set (Sym2 W)) (A : Set W) (x : Fin 3 → Sym2 W)
  (a b : Fin 3 → W)

/-- A component of `K` is closed under `K`-adjacency. -/
theorem reach_closed {S : Set W} {u : W} (hu : u ∈ S)
    (hclosed : ∀ p, p ∈ S → ∀ q, KAdjT H X A x p q → q ∈ S)
    {v : W} (h : Relation.ReflTransGen (KAdjT H X A x) u v) : v ∈ S := by
  induction h with
  | refl => exact hu
  | tail _ hbc ih => exact hclosed _ ih _ hbc

/-- Every index is one of three distinct indices of `Fin 3`. -/
theorem fin3_cases : ∀ i j k n : Fin 3, i ≠ j → i ≠ k → j ≠ k → n = i ∨ n = j ∨ n = k := by
  decide


/-- The data the auxiliary graph `K` carries at this point of the proof of 5.7 (4). -/
structure Setup (H : SimpleGraph W) (X : Set (Sym2 W)) (A : Set W) (x : Fin 3 → Sym2 W)
    (a b : Fin 3 → W) : Prop where
  /-- `aᵢ, bᵢ` are the two ends of the marked edge `xᵢ`. -/
  hab : ∀ i, x i = s(a i, b i)
  /-- The three marked edges are disjoint. -/
  hdist : ∀ i j : Fin 3, i ≠ j → a i ≠ a j ∧ a i ≠ b j ∧ b i ≠ a j ∧ b i ≠ b j
  /-- A marked edge has two distinct ends. -/
  hab_ne : ∀ i, a i ≠ b i
  /-- *"`a₁, a₂, a₃` are pairwise nonadjacent in `K`"*. -/
  hnoaa : ∀ i j : Fin 3, i ≠ j → ¬ KAdj H X A x (a i) (a j)
  /-- *"and similarly so are `b₁, b₂, b₃`"*. -/
  hnobb : ∀ i j : Fin 3, i ≠ j → ¬ KAdj H X A x (b i) (b j)
  /-- *"`a₃` is not adjacent in `K` to both `b₁` and `b₂`, and five similar statements"*. -/
  hnd : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → ∀ u v w : W,
      u ∈ x k → v ∈ x i → w ∈ x j → KAdj H X A x u v → KAdj H X A x u w → False
  /-- *"each `xᵢ` has at least one end in `V(A)`"*. -/
  hmeetA : ∀ i, a i ∈ A ∨ b i ∈ A
  /-- *"there is a component of `K` containing an end of each of these three edges"*. -/
  hreach : ∀ u v : W, u ∈ A → v ∈ A → u ∈ Terminals x → v ∈ Terminals x →
      Relation.ReflTransGen (KAdjT H X A x) u v

variable {H X A x a b}

theorem mem_a (hs : Setup H X A x a b) (i : Fin 3) : a i ∈ x i := by
  rw [hs.hab i]; exact Sym2.mem_mk_left _ _

theorem mem_b (hs : Setup H X A x a b) (i : Fin 3) : b i ∈ x i := by
  rw [hs.hab i]; exact Sym2.mem_mk_right _ _

theorem term_a (hs : Setup H X A x a b) (i : Fin 3) : a i ∈ Terminals x := ⟨i, mem_a hs i⟩

theorem term_b (hs : Setup H X A x a b) (i : Fin 3) : b i ∈ Terminals x := ⟨i, mem_b hs i⟩

theorem terminal_cases (hs : Setup H X A x a b) {z : W} (hz : z ∈ Terminals x) :
    ∃ m, z = a m ∨ z = b m := by
  obtain ⟨m, hm⟩ := hz
  rw [hs.hab m] at hm
  exact ⟨m, Sym2.mem_iff.mp hm⟩

/-- No marked edge is isolated in `K`: some other marked edge has an end joined to one of its
ends.  Otherwise its two ends are a component of `K` on their own, and no component of `K` can
then meet all three marked edges. -/
theorem not_isolated (hs : Setup H X A x a b) (m : Fin 3) :
    ∃ n, n ≠ m ∧ (KAdj H X A x (a m) (b n) ∨ KAdj H X A x (b m) (a n)) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨n, hnm⟩ : ∃ n : Fin 3, n ≠ m := exists_ne m
  have hno : ∀ n' : Fin 3, n' ≠ m →
      ¬ KAdj H X A x (a m) (b n') ∧ ¬ KAdj H X A x (b m) (a n') := hcon
  -- the two ends of `x m` form a component of `K`
  have hclosed : ∀ p, p ∈ ({a m, b m} : Set W) → ∀ q, KAdjT H X A x p q →
      q ∈ ({a m, b m} : Set W) := by
    rintro p (rfl | rfl) q ⟨-, hqT, hadj⟩ <;>
      · obtain ⟨n', hn' | hn'⟩ := terminal_cases hs hqT
        all_goals subst hn'
        all_goals by_cases hnm' : n' = m
        all_goals subst_vars
        all_goals first
          | (left; rfl)
          | (right; rfl)
          | exact absurd hadj (hs.hnoaa _ _ (Ne.symm hnm'))
          | exact absurd hadj (hs.hnobb _ _ (Ne.symm hnm'))
          | exact absurd hadj (hno n' hnm').1
          | exact absurd hadj (hno n' hnm').2
  -- but the component of `K` meets `x n` as well
  obtain htm | htm := hs.hmeetA m <;> obtain htn | htn := hs.hmeetA n
  all_goals
    first
    | (have hmem := reach_closed H X A x (S := ({a m, b m} : Set W)) (by simp) hclosed
        (hs.hreach _ _ htm htn (by first | exact term_a hs m | exact term_b hs m)
          (by first | exact term_a hs n | exact term_b hs n))
       rcases hmem with h | h
       · first
         | exact (hs.hdist n m hnm).1 h
         | exact (hs.hdist n m hnm).2.2.1 h
       · first
         | exact (hs.hdist n m hnm).2.1 h
         | exact (hs.hdist n m hnm).2.2.2 h)

/-- The configuration of the printed proof, given two `K`-edges out of the two ends of one
marked edge.  If that marked edge is itself an edge of `K` we are already done; otherwise the
component of `K` forces the marked edge reached from `a k` to have the property instead. -/
theorem key (hs : Setup H X A x a b) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (h1 : KAdj H X A x (a k) (b i)) (h2 : KAdj H X A x (b k) (a j)) :
    ∃ i' j' k' : Fin 3, i' ≠ j' ∧ i' ≠ k' ∧ j' ≠ k' ∧
      KAdj H X A x (a k') (b k') ∧ KAdj H X A x (a k') (b j') ∧
      KAdj H X A x (a i') (b k') := by
  have hakA : a k ∈ A := kAdj_mem_left h1
  have hbkA : b k ∈ A := kAdj_mem_left h2
  by_cases hown : KAdj H X A x (a k) (b k)
  · exact ⟨j, i, k, Ne.symm hij, hjk, hik, hown, h1, kAdj_symm h2⟩
  -- the neighbours of `a k` in `K`
  have hNak : ∀ q : W, KAdjT H X A x (a k) q → q = a k ∨ q = b i := by
    rintro q ⟨-, hqT, hadj⟩
    obtain ⟨n, hn | hn⟩ := terminal_cases hs hqT
    · subst hn
      by_cases hnk : n = k
      · subst hnk; exact Or.inl rfl
      · exact absurd hadj (hs.hnoaa k n (Ne.symm hnk))
    · subst hn
      rcases fin3_cases i j k n hij hik hjk with hn | hn | hn
      · subst hn; exact Or.inr rfl
      · subst hn
        exact absurd (hs.hnd i n k hij hik hjk (a k) (b i) (b n)
          (mem_a hs k) (mem_b hs i) (mem_b hs n) h1 hadj) id
      · subst hn; exact absurd hadj hown
  -- the neighbours of `b i` in `K`, given that `x i` is not an edge of `K`
  have hNbi : ¬ KAdj H X A x (a i) (b i) →
      ∀ q : W, KAdjT H X A x (b i) q → q = a k ∨ q = b i := by
    intro hno q hq
    obtain ⟨-, hqT, hadj⟩ := hq
    obtain ⟨n, hn | hn⟩ := terminal_cases hs hqT
    · subst hn
      rcases fin3_cases i j k n hij hik hjk with hn | hn | hn
      · subst hn; exact absurd (kAdj_symm hadj) hno
      · subst hn
        exact absurd (hs.hnd n k i hjk (Ne.symm hij) (Ne.symm hik) (b i) (a n) (a k)
          (mem_b hs i) (mem_a hs n) (mem_a hs k) hadj (kAdj_symm h1)) id
      · subst hn; exact Or.inl rfl
    · subst hn
      by_cases hni : n = i
      · subst hni; exact Or.inr rfl
      · exact absurd hadj (hs.hnobb i n (Ne.symm hni))
  -- `x i` is an edge of `K`
  have howni : KAdj H X A x (a i) (b i) := by
    by_contra hno
    have hclosed : ∀ p, p ∈ ({a k, b i} : Set W) → ∀ q, KAdjT H X A x p q →
        q ∈ ({a k, b i} : Set W) := by
      rintro p (rfl | rfl) q hq
      · exact hNak q hq
      · exact hNbi hno q hq
    have hmem := reach_closed H X A x (S := ({a k, b i} : Set W)) (by simp) hclosed
      (hs.hreach (a k) (b k) hakA hbkA (term_a hs k) (term_b hs k))
    rcases hmem with h | h
    · exact (hs.hab_ne k) h.symm
    · exact (hs.hdist k i (Ne.symm hik)).2.2.2 h
  -- `a i` has a `K`-neighbour outside `x i` and outside `x k`
  have hij' : KAdj H X A x (a i) (b j) := by
    by_contra hno2
    have hNai : ∀ q : W, KAdjT H X A x (a i) q → q ∈ ({a k, b i, a i} : Set W) := by
      rintro q ⟨-, hqT, hadj⟩
      obtain ⟨n, hn | hn⟩ := terminal_cases hs hqT
      · subst hn
        by_cases hni : n = i
        · subst hni; exact Or.inr (Or.inr rfl)
        · exact absurd hadj (hs.hnoaa i n (Ne.symm hni))
      · subst hn
        rcases fin3_cases i j k n hij hik hjk with hn | hn | hn
        · subst hn; exact Or.inr (Or.inl rfl)
        · subst hn; exact absurd hadj hno2
        · subst hn
          exact absurd (hs.hnd j i n (Ne.symm hij) hjk hik (b n) (a j) (a i)
            (mem_b hs n) (mem_a hs j) (mem_a hs i) h2 (kAdj_symm hadj)) id
    have hclosed : ∀ p, p ∈ ({a k, b i, a i} : Set W) → ∀ q, KAdjT H X A x p q →
        q ∈ ({a k, b i, a i} : Set W) := by
      rintro p (rfl | rfl | rfl) q hq
      · rcases hNak q hq with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · obtain ⟨-, hqT, hadj⟩ := hq
        obtain ⟨n, hn | hn⟩ := terminal_cases hs hqT
        · subst hn
          rcases fin3_cases i j k n hij hik hjk with hn | hn | hn
          · subst hn; exact Or.inr (Or.inr rfl)
          · subst hn
            exact absurd (hs.hnd n k i hjk (Ne.symm hij) (Ne.symm hik) (b i) (a n) (a k)
              (mem_b hs i) (mem_a hs n) (mem_a hs k) hadj (kAdj_symm h1)) id
          · subst hn; exact Or.inl rfl
        · subst hn
          by_cases hni : n = i
          · subst hni; exact Or.inr (Or.inl rfl)
          · exact absurd hadj (hs.hnobb i n (Ne.symm hni))
      · exact hNai q hq
    have hmem := reach_closed H X A x (S := ({a k, b i, a i} : Set W)) (by simp) hclosed
      (hs.hreach (a k) (b k) hakA hbkA (term_a hs k) (term_b hs k))
    rcases hmem with h | h | h
    · exact (hs.hab_ne k) h.symm
    · exact (hs.hdist k i (Ne.symm hik)).2.2.2 h
    · exact (hs.hdist k i (Ne.symm hik)).2.2.1 h
  exact ⟨k, j, i, Ne.symm hjk, Ne.symm hik, Ne.symm hij, howni, hij', h1⟩

/-- **The configuration of the printed proof.**  There are three distinct indices `i, j, k`
such that the marked edge `x k` is an edge of `K`, `a k` is joined in `K` to `b j`, and `a i`
is joined in `K` to `b k`.  This is the paper's *"we may assume that `a₁b₃, b₂a₃, a₃b₃ ∈
E(K)`"*. -/
theorem exists_config (hs : Setup H X A x a b) :
    ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      KAdj H X A x (a k) (b k) ∧ KAdj H X A x (a k) (b j) ∧
      KAdj H X A x (a i) (b k) := by
  -- some marked edge is joined in `K` to both others
  obtain ⟨k, i, j, hij, hik, hjk, hEi, hEj⟩ :
      ∃ k i j : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
        (KAdj H X A x (a k) (b i) ∨ KAdj H X A x (b k) (a i)) ∧
        (KAdj H X A x (a k) (b j) ∨ KAdj H X A x (b k) (a j)) := by
    obtain ⟨n₀, hn₀, hE₀⟩ := not_isolated hs 0
    obtain ⟨n₁, hn₁, hE₁⟩ := not_isolated hs 1
    obtain ⟨n₂, hn₂, hE₂⟩ := not_isolated hs 2
    have hswap : ∀ m n : Fin 3,
        (KAdj H X A x (a m) (b n) ∨ KAdj H X A x (b m) (a n)) →
        (KAdj H X A x (a n) (b m) ∨ KAdj H X A x (b n) (a m)) := by
      intro m n h
      rcases h with h | h
      · exact Or.inr (kAdj_symm h)
      · exact Or.inl (kAdj_symm h)
    have h30 : ∀ n : Fin 3, n ≠ 0 → n = 1 ∨ n = 2 := by decide
    have h31 : ∀ n : Fin 3, n ≠ 1 → n = 0 ∨ n = 2 := by decide
    have h32 : ∀ n : Fin 3, n ≠ 2 → n = 0 ∨ n = 1 := by decide
    rcases h30 n₀ hn₀ with rfl | rfl
    · rcases h32 n₂ hn₂ with rfl | rfl
      · exact ⟨0, 1, 2, by decide, by decide, by decide, hE₀, hswap _ _ hE₂⟩
      · exact ⟨1, 0, 2, by decide, by decide, by decide, hswap _ _ hE₀, hswap _ _ hE₂⟩
    · rcases h31 n₁ hn₁ with rfl | rfl
      · exact ⟨0, 1, 2, by decide, by decide, by decide, hswap _ _ hE₁, hE₀⟩
      · exact ⟨2, 0, 1, by decide, by decide, by decide, hswap _ _ hE₀, hswap _ _ hE₁⟩
  -- the two `K`-edges leave from different ends of `x k`
  rcases hEi with hi | hi <;> rcases hEj with hj | hj
  · exact absurd (hs.hnd i j k hij hik hjk (a k) (b i) (b j)
      (mem_a hs k) (mem_b hs i) (mem_b hs j) hi hj) id
  · exact key hs hij hik hjk hi hj
  · exact key hs (Ne.symm hij) hjk hik hj hi
  · exact absurd (hs.hnd i j k hij hik hjk (b k) (a i) (a j)
      (mem_b hs k) (mem_a hs i) (mem_a hs j) hi hj) id

end Workspace.ProofLemmas.Thm57Claim4Component
