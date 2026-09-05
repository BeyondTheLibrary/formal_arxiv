/-  Proof attempt for statement 24.1 of Chudnovsky-Robertson-Seymour-Thomas,
    *The Strong Perfect Graph Theorem* (published / Annals version, printed p. 143).

    THE PAPER'S PROOF (paper/proofs/24_1.md, `## DEFERRED PROOF`, printed p. 146):

      "Proof of 24.1.  Let G in F11, admitting no balanced skew partition.  We may
       assume that G is not bipartite, and therefore has a triangle.  Consequently we
       may choose disjoint nonempty anticonnected sets X1,...,Xk, complete to each
       other, with k >= 3, with maximal union.  Suppose first that X1 u ... u Xk /=
       V(G), and let F = V(G) \ (X1 u ... u Xk).  By 15.2 (applied to Xk and
       X1 u ... u X(k-1)), F is connected and every vertex of X1 u X2 has a neighbour
       in it.  By 24.7, some vertex v in F is complete to two of X1, X2, X3.  We may
       assume that for some i with 2 <= i <= k, v is Xj-complete for 1 <= j <= i and
       not Xj-complete for i < j <= k.  Define X'(i+1) = X(i+1) u ... u Xk u {v}; then
       the sets X1,...,Xi,X'(i+1) violate the optimality of the choice of X1,...,Xk.
       Hence X1 u ... u Xk = V(G), and therefore Gbar has at least three components.
       From 15.2 it follows that G is complete.  This proves 24.1."

    This is the PUBLISHED argument (the arXiv v1 draft of section 24 was rewritten:
    it used an auxiliary set N and split on X_k u N = V(G); see paper/pdf/S24_The_end.md,
    "Notes / discrepancies", item 1).

    HOW IT MAPS ONTO THE LEAN PROOF.

    * The unordered family {X1,...,Xk} is a `𝒳 : Set (Set V)` satisfying `GoodFam`
      (three distinct members = "k >= 3"; disjoint, nonempty, anticonnected, complete
      to each other).  Keeping the family unordered is what makes the paper's implicit
      renumbering ("we may assume that for some i ... v is Xj-complete for 1 <= j <= i")
      free: the renumbering is just the partition of `𝒳` into the members `v` is
      complete to (`𝒵`) and the rest (`𝒴`).
    * "with maximal union" is a maximum of `(⋃₀ 𝒳).ncard`, which exists because that
      quantity is bounded by `Nat.card V` (`Nat.sSup_mem`).
    * "We may assume that G is not bipartite, and therefore has a triangle" is the
      private lemma `exists_triangle_of_not_bipartite`: a non-2-colourable graph has an
      odd closed walk, a shortest one is an induced odd cycle, and a Berge graph has no
      odd hole, so that cycle has exactly three vertices.
    * "By 15.2 (applied to Xk and X1 u ... u X(k-1))" is `thm_15_2` with
      `X := ⋃ (𝒳 \ {C})` and `Y := C`; its second bullet gives that `F` is connected
      and -- since `X` contains two disjoint nonempty members, so is nontrivial --
      that every vertex of `X` (in particular of `A` and of `B`) has a neighbour in `F`.
    * "By 24.7, some vertex v in F is complete to two of X1,X2,X3" is `thm_24_7`.
    * "the sets X1,...,Xi,X'(i+1) violate the optimality" is `hgood'` together with
      `hUnion`: the new family is `insert W 𝒵` with `W = (⋃₀ 𝒴) ∪ {v}`, and its union
      is `insert v (⋃₀ 𝒳)`, of strictly larger cardinality.
    * "therefore Gbar has at least three components.  From 15.2 it follows that G is
      complete" is the first bullet of `thm_15_2`: each member of `𝒳` is an
      anticomponent of `V(G)`, and there are three distinct ones, so the alternative
      "Gbar has exactly two components" is impossible.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.Classes
import Workspace.Statements.S15.Thm_15_2
import Workspace.Statements.S24.Thm_24_7

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S24

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

/-- Filling the paper's implicit step *"We may assume that `G` is not bipartite, and
therefore has a triangle."* -/
private theorem exists_triangle_of_not_bipartite {V : Type*}
    (G : SimpleGraph V) (hB : Berge G) (hnb : ¬ G.IsBipartite) :
    ∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a := by
  classical
  -- 1. a closed walk of odd length exists
  have hodd : ∃ (x : V) (q : G.Walk x x), Odd q.length := by
    by_contra hcon
    push Not at hcon
    exact hnb (SimpleGraph.two_colorable_iff_forall_loop_even.2
      (fun x q => Nat.not_odd_iff_even.mp (hcon x q)))
  have hexP : ∃ m : ℕ, ∃ (x : V) (q : G.Walk x x), q.length = m ∧ Odd m := by
    obtain ⟨x, q, hq⟩ := hodd
    exact ⟨q.length, x, q, rfl, hq⟩
  obtain ⟨n, ⟨u, w, hwlen, hnodd⟩, hmin⟩ :
      ∃ n : ℕ, (∃ (x : V) (q : G.Walk x x), q.length = n ∧ Odd n) ∧
        (∀ (x : V) (q : G.Walk x x), Odd q.length → n ≤ q.length) := by
    refine ⟨Nat.find hexP, Nat.find_spec hexP, ?_⟩
    intro x q hq
    exact Nat.find_min' hexP ⟨x, q, rfl, hq⟩
  have hpar : n % 2 = 1 := Nat.odd_iff.mp hnodd
  have hu0 : w.getVert 0 = u := w.getVert_zero
  have hun : w.getVert n = u := by rw [← hwlen]; exact w.getVert_length
  have hadjsucc : ∀ i, i < n → G.Adj (w.getVert i) (w.getVert (i + 1)) := by
    intro i hi
    exact w.adj_getVert_succ (by omega)
  -- 2. `n ≥ 3`
  have hn3 : 3 ≤ n := by
    by_contra hlt
    have hn1 : n = 1 := by omega
    have h1 : G.Adj (w.getVert 0) (w.getVert 1) := hadjsucc 0 (by omega)
    rw [hu0, show (1 : ℕ) = n from hn1.symm, hun] at h1
    exact G.irrefl h1
  -- 3. the two sub-walks
  have hseg : ∀ i j : ℕ, i ≤ j → j ≤ n →
      ∃ q : G.Walk (w.getVert i) (w.getVert j), q.length = j - i := by
    intro i j hij hjn
    refine ⟨((w.drop i).take (j - i)).copy rfl ?_, ?_⟩
    · rw [SimpleGraph.Walk.drop_getVert]
      congr 1
      omega
    · rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.take_length,
        SimpleGraph.Walk.drop_length, hwlen]
      omega
  have hrest : ∀ i j : ℕ, i ≤ n → j ≤ n →
      ∃ q : G.Walk (w.getVert j) (w.getVert i), q.length = n - j + i := by
    intro i j hin hjn
    refine ⟨(w.drop j).append (w.take i), ?_⟩
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.drop_length,
      SimpleGraph.Walk.take_length, hwlen]
    omega
  -- 4. the vertices `getVert 0, …, getVert (n-1)` are distinct
  have hinj : ∀ i j : ℕ, i < j → j < n → w.getVert i ≠ w.getVert j := by
    intro i j hij hjn heq
    obtain ⟨qa, hqa⟩ := hseg i j (le_of_lt hij) (by omega)
    obtain ⟨qb, hqb⟩ := hrest i j (by omega) (by omega)
    have hcase : (j - i) % 2 = 1 ∨ (n - j + i) % 2 = 1 := by omega
    rcases hcase with h | h
    · have hle := hmin _ (qa.copy rfl heq.symm)
        (Nat.odd_iff.mpr (by rw [SimpleGraph.Walk.length_copy, hqa]; exact h))
      rw [SimpleGraph.Walk.length_copy, hqa] at hle
      omega
    · have hle := hmin _ (qb.copy heq.symm rfl)
        (Nat.odd_iff.mpr (by rw [SimpleGraph.Walk.length_copy, hqb]; exact h))
      rw [SimpleGraph.Walk.length_copy, hqb] at hle
      omega
  -- 5. no chords
  have hchord : ∀ i j : ℕ, i < j → j < n → G.Adj (w.getVert i) (w.getVert j) →
      (j = i + 1 ∨ (i = 0 ∧ j = n - 1)) := by
    intro i j hij hjn hadj
    by_contra hcon
    have hne1 : j ≠ i + 1 := fun h => hcon (Or.inl h)
    have hne2 : ¬ (i = 0 ∧ j = n - 1) := fun h => hcon (Or.inr h)
    obtain ⟨qa, hqa⟩ := hseg i j (le_of_lt hij) (by omega)
    obtain ⟨qb, hqb⟩ := hrest i j (by omega) (by omega)
    have hcase : (j - i + 1) % 2 = 1 ∨ (n - j + i + 1) % 2 = 1 := by omega
    rcases hcase with h | h
    · have hle := hmin _ (qa.concat hadj.symm)
        (Nat.odd_iff.mpr (by rw [SimpleGraph.Walk.length_concat, hqa]; exact h))
      rw [SimpleGraph.Walk.length_concat, hqa] at hle
      omega
    · have hle := hmin _ (qb.concat hadj)
        (Nat.odd_iff.mpr (by rw [SimpleGraph.Walk.length_concat, hqb]; exact h))
      rw [SimpleGraph.Walk.length_concat, hqb] at hle
      omega
  -- 6. package as a list
  have hu0n : w.getVert n = w.getVert 0 := hun.trans hu0.symm
  have hwrap : G.Adj (w.getVert (n - 1)) (w.getVert 0) := by
    have h := hadjsucc (n - 1) (by omega)
    rw [show n - 1 + 1 = n by omega, hu0n] at h
    exact h
  have hmod : ∀ k : ℕ, k < n → (k + 1) % n = if k + 1 = n then 0 else k + 1 := by
    intro k hk
    by_cases hh : k + 1 = n
    · simp [hh]
    · rw [if_neg hh, Nat.mod_eq_of_lt (by omega)]
  have hLnd0 : ((List.range n).map w.getVert).Nodup := by
    refine List.Nodup.map_on ?_ List.nodup_range
    intro x hx y hy hxy
    simp only [List.mem_range] at hx hy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hinj x y h hy hxy
    · exact hinj y x h hx hxy.symm
  obtain ⟨L, hclen, hcnd, hcget⟩ : ∃ L : List V, L.length = n ∧ L.Nodup ∧
      ∀ (i : ℕ) (hi : i < L.length), (L[i]'hi) = w.getVert i :=
    ⟨(List.range n).map w.getVert, by simp, hLnd0, by intro i hi; simp⟩
  have hcadj : ∀ (i j : ℕ) (hi : i < L.length) (hj : j < L.length),
      (G.Adj (L[i]'hi) (L[j]'hj) ↔ (j = (i + 1) % L.length ∨ i = (j + 1) % L.length)) := by
    intro i j hi hj
    have hi' : i < n := by omega
    have hj' : j < n := by omega
    rw [hcget i hi, hcget j hj, hclen, hmod i hi', hmod j hj']
    constructor
    · intro hadj
      have hne : i ≠ j := by
        rintro rfl
        exact G.irrefl hadj
      rcases lt_or_gt_of_ne hne with h | h
      · rcases hchord i j h hj' hadj with h1 | ⟨h1, h2⟩
        · left; split_ifs <;> omega
        · right; split_ifs <;> omega
      · rcases hchord j i h hi' hadj.symm with h1 | ⟨h1, h2⟩
        · right; split_ifs <;> omega
        · left; split_ifs <;> omega
    · intro hcyc
      split_ifs at hcyc with h1 h2 h2
      · -- i + 1 = n and j + 1 = n : impossible (i = j)
        exfalso; omega
      · rcases hcyc with h | h
        · rw [h, show i = n - 1 by omega]; exact hwrap
        · rw [h]; exact (hadjsucc j hj').symm
      · rcases hcyc with h | h
        · rw [h]; exact hadjsucc i hi'
        · rw [h, show j = n - 1 by omega]; exact hwrap.symm
      · rcases hcyc with h | h
        · rw [h]; exact hadjsucc i hi'
        · rw [h]; exact (hadjsucc j hj').symm
  -- 7. Berge forbids an odd hole, so `n = 3`
  have hn3' : n = 3 := by
    by_contra hne
    have hhole : IsHoleList G L := ⟨by omega, hcnd, hcadj⟩
    have heven := hB.1 L hhole
    rw [holeLength, hclen] at heven
    rw [Nat.even_iff] at heven
    omega
  refine ⟨w.getVert 0, w.getVert 1, w.getVert 2, by simpa using hadjsucc 0 (by omega),
    by simpa using hadjsucc 1 (by omega), ?_⟩
  have h := hadjsucc 2 (by omega)
  rw [show (2 : ℕ) + 1 = n by omega, hu0n] at h
  exact h

/-- `Complete` is a symmetric relation between sets. -/
private theorem complete_symm {V : Type*} {G : SimpleGraph V} {X Y : Set V}
    (h : Complete G X Y) : Complete G Y X :=
  fun y hy x hx => (h x hx y hy).symm

/-- Reachability inside an induced subgraph is inherited by any larger induced subgraph. -/
private theorem reachable_induce_mono {V : Type*} {H : SimpleGraph V} {A B : Set V}
    (hAB : A ⊆ B) {x y : V} (hx : x ∈ A) (hy : y ∈ A)
    (hr : (H.induce A).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    (H.induce B).Reachable ⟨x, hAB hx⟩ ⟨y, hAB hy⟩ := by
  obtain ⟨p⟩ := hr
  exact ⟨SimpleGraph.Walk.map
    (⟨fun z => ⟨z.1, hAB z.2⟩, fun {_ _} hab => hab⟩ : (H.induce A) →g (H.induce B)) p⟩

/-- If no edge of `H` leaves `E` inside `D`, a walk of `H|D` starting in `E` stays in `E`. -/
private theorem walk_stays {V : Type*} {H : SimpleGraph V} {D E : Set V}
    (hclosed : ∀ a ∈ E, ∀ b ∈ D, H.Adj a b → b ∈ E)
    {x y : ↥D} (p : (H.induce D).Walk x y) (hx : (x : V) ∈ E) : (y : V) ∈ E := by
  revert hx
  induction p with
  | nil => exact fun h => h
  | @cons a b _ hab _ ih => exact fun ha => ih (hclosed _ ha _ b.2 hab)

/-- The paper's *"disjoint nonempty anticonnected sets `X₁, …, X_k`, complete to each other,
with `k ≥ 3`"*, recorded as an unordered family of sets (so that the paper's implicit
renumbering of the `Xᵢ` costs nothing). -/
private def GoodFam {V : Type*} (G : SimpleGraph V) (𝒳 : Set (Set V)) : Prop :=
  (∃ A B C : Set V, A ∈ 𝒳 ∧ B ∈ 𝒳 ∧ C ∈ 𝒳 ∧ A ≠ B ∧ A ≠ C ∧ B ≠ C) ∧
  (∀ A ∈ 𝒳, A.Nonempty) ∧
  (∀ A ∈ 𝒳, AnticonnectedSet G A) ∧
  (∀ A ∈ 𝒳, ∀ B ∈ 𝒳, A ≠ B → Disjoint A B) ∧
  (∀ A ∈ 𝒳, ∀ B ∈ 𝒳, A ≠ B → Complete G A B)

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **24.1** — the last of the twelve main steps: this is statement **1.8.12**, and
the terminal conclusion of the whole paper (printed p. 143).

PAPER: *"Let `G ∈ F₁₁`; then either `G` is complete, or `G` is bipartite, or `G`
admits a balanced skew partition."* -/
theorem thm_24_1 (G : SimpleGraph V) (hG : InF11 G) :
    (∀ u v : V, u ≠ v → G.Adj u v) ∨ G.IsBipartite ∨ AdmitsBalancedSkewPartition G := by
  classical
  by_cases hbip : G.IsBipartite
  · exact Or.inr (Or.inl hbip)
  by_cases hbsp : AdmitsBalancedSkewPartition G
  · exact Or.inr (Or.inr hbsp)
  refine Or.inl ?_
  have hF6 : InF6 G := hG.1.1.1.1.1
  have hBerge : Berge G := hG.1.1.1.1.1.1.1.1
  -- "We may assume that `G` is not bipartite, and therefore has a triangle."
  obtain ⟨a, b, d, hab, hbd, hda⟩ := exists_triangle_of_not_bipartite G hBerge hbip
  have hsingle : ∀ x : V, AnticonnectedSet G ({x} : Set V) := by
    intro x p q
    have h : p = q := Subtype.ext (p.2.trans q.2.symm)
    exact h ▸ SimpleGraph.Reachable.refl p
  -- "Consequently we may choose disjoint nonempty anticonnected sets `X₁,…,X_k`,
  -- complete to each other, with `k ≥ 3`, with maximal union."
  have hab' : a ≠ b := hab.ne
  have hbd' : b ≠ d := hbd.ne
  have had' : a ≠ d := (hda.ne).symm
  have hmem3 : ∀ E ∈ ({({a} : Set V), {b}, {d}} : Set (Set V)),
      E = {a} ∨ E = {b} ∨ E = {d} := by
    intro E hE
    simpa using hE
  have hgood0 : GoodFam G ({({a} : Set V), {b}, {d}} : Set (Set V)) := by
    refine ⟨⟨{a}, {b}, {d}, by simp, by simp, by simp, by simpa using hab',
      by simpa using had', by simpa using hbd'⟩, ?_, ?_, ?_, ?_⟩
    · intro E hE
      rcases hmem3 E hE with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
    · intro E hE
      rcases hmem3 E hE with rfl | rfl | rfl <;> exact hsingle _
    · intro E hE E' hE' hEE'
      rcases hmem3 E hE with rfl | rfl | rfl <;> rcases hmem3 E' hE' with rfl | rfl | rfl <;>
        first
          | exact absurd rfl hEE'
          | (rw [Set.disjoint_singleton]; assumption)
          | (rw [Set.disjoint_singleton]; exact Ne.symm (by assumption))
    · intro E hE E' hE' hEE'
      rcases hmem3 E hE with rfl | rfl | rfl <;> rcases hmem3 E' hE' with rfl | rfl | rfl <;>
        first
          | exact absurd rfl hEE'
          | (intro x hx y hy
             simp only [Set.mem_singleton_iff] at hx hy
             subst hx; subst hy
             first
               | exact hab | exact hbd | exact hda
               | exact hab.symm | exact hbd.symm | exact hda.symm)
  obtain ⟨𝒳, hgood, hmax⟩ : ∃ 𝒳 : Set (Set V), GoodFam G 𝒳 ∧
      ∀ 𝒴 : Set (Set V), GoodFam G 𝒴 → (⋃₀ 𝒴).ncard ≤ (⋃₀ 𝒳).ncard := by
    have hSne : {m : ℕ | ∃ 𝒴 : Set (Set V), GoodFam G 𝒴 ∧ (⋃₀ 𝒴).ncard = m}.Nonempty :=
      ⟨_, _, hgood0, rfl⟩
    have hSbdd : BddAbove {m : ℕ | ∃ 𝒴 : Set (Set V), GoodFam G 𝒴 ∧ (⋃₀ 𝒴).ncard = m} := by
      refine ⟨Nat.card V, ?_⟩
      rintro m ⟨𝒴, -, rfl⟩
      rw [← Set.ncard_univ]
      exact Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
    obtain ⟨𝒳, hgood, hcard⟩ := Nat.sSup_mem hSne hSbdd
    refine ⟨𝒳, hgood, fun 𝒴 h𝒴 => ?_⟩
    rw [hcard]
    exact le_csSup hSbdd ⟨𝒴, h𝒴, rfl⟩
  obtain ⟨A, B, C, hA, hB, hC, hABne, hACne, hBCne⟩ := hgood.1
  have hne : ∀ E ∈ 𝒳, E.Nonempty := hgood.2.1
  have hanti : ∀ E ∈ 𝒳, AnticonnectedSet G E := hgood.2.2.1
  have hdisj : ∀ E ∈ 𝒳, ∀ E' ∈ 𝒳, E ≠ E' → Disjoint E E' := hgood.2.2.2.1
  have hcompl : ∀ E ∈ 𝒳, ∀ E' ∈ 𝒳, E ≠ E' → Complete G E E' := hgood.2.2.2.2
  -- 15.2 will be applied to `X_k` (here `C`) and `X₁ ∪ ⋯ ∪ X_{k-1}` (here `X`).
  obtain ⟨X, hmemX⟩ : ∃ X : Set V, ∀ z : V, z ∈ X ↔ ∃ E ∈ 𝒳, E ≠ C ∧ z ∈ E := by
    refine ⟨⋃₀ (𝒳 \ {C}), fun z => ⟨?_, ?_⟩⟩
    · rintro ⟨E, ⟨hE, hEC⟩, hz⟩
      exact ⟨E, hE, hEC, hz⟩
    · rintro ⟨E, hE, hEC, hz⟩
      exact ⟨E, ⟨hE, hEC⟩, hz⟩
  obtain ⟨a₀, ha₀⟩ := hne A hA
  obtain ⟨b₀, hb₀⟩ := hne B hB
  have haX : a₀ ∈ X := (hmemX a₀).mpr ⟨A, hA, hACne, ha₀⟩
  have hbX : b₀ ∈ X := (hmemX b₀).mpr ⟨B, hB, hBCne, hb₀⟩
  have hXne : X.Nonempty := ⟨a₀, haX⟩
  have hXnt : X.Nontrivial := by
    refine ⟨a₀, haX, b₀, hbX, ?_⟩
    intro h
    subst h
    exact (Set.disjoint_left.mp (hdisj A hA B hB hABne) ha₀) hb₀
  have hCne : C.Nonempty := hne C hC
  have hXCdisj : Disjoint X C := by
    rw [Set.disjoint_left]
    intro z hz hzC
    obtain ⟨E, hE, hEC, hzE⟩ := (hmemX z).mp hz
    exact (Set.disjoint_left.mp (hdisj E hE C hC hEC) hzE) hzC
  have hXCcompl : Complete G X C := by
    intro z hz y hy
    obtain ⟨E, hE, hEC, hzE⟩ := (hmemX z).mp hz
    exact hcompl E hE C hC hEC z hzE y hy
  have hXCunion : X ∪ C = ⋃₀ 𝒳 := by
    apply Set.Subset.antisymm
    · rintro z (hz | hz)
      · obtain ⟨E, hE, -, hzE⟩ := (hmemX z).mp hz
        exact ⟨E, hE, hzE⟩
      · exact ⟨C, hC, hz⟩
    · rintro z ⟨E, hE, hzE⟩
      by_cases h : E = C
      · exact Or.inr (h ▸ hzE)
      · exact Or.inl ((hmemX z).mpr ⟨E, hE, h, hzE⟩)
  have h152 := _root_.Workspace.Statements.S15.SPGT.thm_15_2 G hF6 hbsp X C hXne hCne
    hXCdisj hXCcompl
  by_cases hUuniv : (⋃₀ 𝒳) = Set.univ
  · -- "Hence `X₁ ∪ ⋯ ∪ X_k = V(G)`, and therefore `Ḡ` has at least three components.
    -- From 15.2 it follows that `G` is complete."
    rcases h152.1 (by rw [hXCunion]; exact hUuniv) with hcomp | ⟨⟨B₁, B₂, -, -, -, hall⟩, -⟩
    · exact hcomp
    · exfalso
      have hAnti : ∀ E ∈ 𝒳, IsAnticomponent G Set.univ E := by
        intro E hE
        refine ⟨Set.subset_univ E, hanti E hE, ?_⟩
        intro D hED _ hDconn
        refine Set.Subset.antisymm ?_ hED
        intro z hz
        obtain ⟨e, he⟩ := hne E hE
        have hclosed : ∀ x ∈ E, ∀ y ∈ D, Gᶜ.Adj x y → y ∈ E := by
          intro x hx y _ hadj
          have hyU : y ∈ (⋃₀ 𝒳) := by rw [hUuniv]; trivial
          obtain ⟨E', hE', hyE'⟩ := hyU
          by_cases hEE' : E' = E
          · exact hEE' ▸ hyE'
          · exact absurd (hcompl E hE E' hE' (Ne.symm hEE') x hx y hyE') hadj.2
        obtain ⟨p⟩ := hDconn ⟨e, hED he⟩ ⟨z, hz⟩
        exact walk_stays hclosed p he
      have h1 := hall A (hAnti A hA)
      have h2 := hall B (hAnti B hB)
      have h3 := hall C (hAnti C hC)
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
      · exact hABne (h1.trans h2.symm)
      · exact hABne (h1.trans h2.symm)
      · exact hACne (h1.trans h3.symm)
      · exact hBCne (h2.trans h3.symm)
      · exact hBCne (h2.trans h3.symm)
      · exact hACne (h1.trans h3.symm)
      · exact hABne (h1.trans h2.symm)
      · exact hABne (h1.trans h2.symm)
  · -- "Suppose first that `X₁ ∪ ⋯ ∪ X_k ≠ V(G)`, and let `F = V(G) \ (X₁ ∪ ⋯ ∪ X_k)`."
    exfalso
    obtain ⟨hFconn, hFnbr⟩ := h152.2 (by rw [hXCunion]; exact hUuniv)
    have hFmem : ∀ z : V, z ∈ (X ∪ C)ᶜ ↔ z ∉ (⋃₀ 𝒳) := by
      intro z; rw [hXCunion]; exact Iff.rfl
    have hFsub : (X ∪ C)ᶜ ⊆ (A ∪ B ∪ C)ᶜ := by
      intro z hz hcon
      refine (hFmem z).mp hz ?_
      rcases hcon with (h | h) | h
      · exact ⟨A, hA, h⟩
      · exact ⟨B, hB, h⟩
      · exact ⟨C, hC, h⟩
    -- "By 24.7, some vertex `v ∈ F` is complete to two of `X₁, X₂, X₃`."
    obtain ⟨v, hvF, hv2⟩ := _root_.Workspace.Statements.S24.SPGT.thm_24_7 G hG hbsp A B C
      (hdisj A hA B hB hABne) (hdisj A hA C hC hACne) (hdisj B hB C hC hBCne)
      (hne A hA) (hne B hB) (hne C hC)
      (hanti A hA) (hanti B hB) (hanti C hC)
      (hcompl A hA B hB hABne) (hcompl A hA C hC hACne) (hcompl B hB C hC hBCne)
      ((X ∪ C)ᶜ) hFsub hFconn
      (Or.inl ⟨fun x hx => hFnbr hXnt x ((hmemX x).mpr ⟨A, hA, hACne, hx⟩),
        fun x hx => hFnbr hXnt x ((hmemX x).mpr ⟨B, hB, hBCne, hx⟩)⟩)
    have hvU : v ∉ (⋃₀ 𝒳) := (hFmem v).mp hvF
    have hvnotE : ∀ E ∈ 𝒳, v ∉ E := fun E hE hvE => hvU ⟨E, hE, hvE⟩
    -- "We may assume that for some `i` with `2 ≤ i ≤ k`, `v` is `X_j`-complete for
    -- `1 ≤ j ≤ i` and not `X_j`-complete for `i < j ≤ k`."
    obtain ⟨𝒴, hmemY⟩ : ∃ 𝒴 : Set (Set V),
        ∀ E : Set V, E ∈ 𝒴 ↔ (E ∈ 𝒳 ∧ ¬ VertexComplete G v E) :=
      ⟨{E ∈ 𝒳 | ¬ VertexComplete G v E}, fun _ => Iff.rfl⟩
    obtain ⟨𝒵, hmemZ⟩ : ∃ 𝒵 : Set (Set V),
        ∀ E : Set V, E ∈ 𝒵 ↔ (E ∈ 𝒳 ∧ VertexComplete G v E) :=
      ⟨{E ∈ 𝒳 | VertexComplete G v E}, fun _ => Iff.rfl⟩
    -- "Define `X'_{i+1} = X_{i+1} ∪ ⋯ ∪ X_k ∪ {v}`."
    obtain ⟨W, hmemW⟩ : ∃ W : Set V, ∀ z : V, z ∈ W ↔ ((∃ E ∈ 𝒴, z ∈ E) ∨ z = v) :=
      ⟨(⋃₀ 𝒴) ∪ {v}, fun z => ⟨fun h => h, fun h => h⟩⟩
    have hvW : v ∈ W := (hmemW v).mpr (Or.inr rfl)
    have hYsub : ∀ E ∈ 𝒴, E ∈ 𝒳 := fun E hE => ((hmemY E).mp hE).1
    have hZsub : ∀ E ∈ 𝒵, E ∈ 𝒳 := fun E hE => ((hmemZ E).mp hE).1
    have hWnotmem : W ∉ 𝒵 := fun h => hvU ⟨W, hZsub W h, hvW⟩
    have hWanti : AnticonnectedSet G W := by
      have hkey : ∀ (z : V) (hz : z ∈ W), (Gᶜ.induce W).Reachable ⟨z, hz⟩ ⟨v, hvW⟩ := by
        intro z hz
        rcases (hmemW z).mp hz with ⟨E, hEY, hzE⟩ | hzv
        · obtain ⟨hEX, hEnc⟩ := (hmemY E).mp hEY
          have hex : ∃ x ∈ E, ¬ G.Adj v x := by
            by_contra hcon
            push Not at hcon
            exact hEnc hcon
          obtain ⟨e, heE, hnadj⟩ := hex
          have hve : Gᶜ.Adj v e := by
            rw [SimpleGraph.compl_adj]
            exact ⟨fun h => hvnotE E hEX (by rw [h]; exact heE), hnadj⟩
          have hEsubW : E ⊆ W := fun y hy => (hmemW y).mpr (Or.inl ⟨E, hEY, hy⟩)
          have h1 : (Gᶜ.induce W).Reachable ⟨z, hEsubW hzE⟩ ⟨e, hEsubW heE⟩ :=
            reachable_induce_mono hEsubW hzE heE (hanti E hEX ⟨z, hzE⟩ ⟨e, heE⟩)
          have h2 : (Gᶜ.induce W).Adj ⟨e, hEsubW heE⟩ ⟨v, hvW⟩ := hve.symm
          exact h1.trans h2.reachable
        · subst hzv
          exact SimpleGraph.Reachable.refl _
      intro p q
      exact (hkey p.1 p.2).trans (hkey q.1 q.2).symm
    have hWdisjZ : ∀ E ∈ 𝒵, Disjoint W E := by
      intro E hE
      rw [Set.disjoint_left]
      intro z hz hzE
      rcases (hmemW z).mp hz with ⟨E', hEY, hzE'⟩ | hzv
      · have hEE' : E' ≠ E := by
          intro h
          subst h
          exact ((hmemY E').mp hEY).2 ((hmemZ E').mp hE).2
        exact (Set.disjoint_left.mp (hdisj E' (hYsub E' hEY) E (hZsub E hE) hEE') hzE') hzE
      · subst hzv
        exact hvnotE E (hZsub E hE) hzE
    have hWcomplZ : ∀ E ∈ 𝒵, Complete G W E := by
      intro E hE z hz y hy
      rcases (hmemW z).mp hz with ⟨E', hEY, hzE'⟩ | hzv
      · have hEE' : E' ≠ E := by
          intro h
          subst h
          exact ((hmemY E').mp hEY).2 ((hmemZ E').mp hE).2
        exact hcompl E' (hYsub E' hEY) E (hZsub E hE) hEE' z hzE' y hy
      · subst hzv
        exact ((hmemZ E).mp hE).2 y hy
    obtain ⟨P, Q, hP, hQ, hPQ⟩ : ∃ P Q : Set V, P ∈ 𝒵 ∧ Q ∈ 𝒵 ∧ P ≠ Q := by
      rcases hv2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨A, B, (hmemZ A).mpr ⟨hA, h1⟩, (hmemZ B).mpr ⟨hB, h2⟩, hABne⟩
      · exact ⟨A, C, (hmemZ A).mpr ⟨hA, h1⟩, (hmemZ C).mpr ⟨hC, h2⟩, hACne⟩
      · exact ⟨B, C, (hmemZ B).mpr ⟨hB, h1⟩, (hmemZ C).mpr ⟨hC, h2⟩, hBCne⟩
    -- "then the sets `X₁, …, X_i, X'_{i+1}` violate the optimality of the choice."
    have hgood' : GoodFam G (insert W 𝒵) := by
      refine ⟨⟨W, P, Q, Set.mem_insert _ _, Set.mem_insert_of_mem _ hP,
        Set.mem_insert_of_mem _ hQ, ?_, ?_, hPQ⟩, ?_, ?_, ?_, ?_⟩
      · intro h; exact hWnotmem (by rw [h]; exact hP)
      · intro h; exact hWnotmem (by rw [h]; exact hQ)
      · rintro E (rfl | hE)
        · exact ⟨v, hvW⟩
        · exact hne E (hZsub E hE)
      · rintro E (rfl | hE)
        · exact hWanti
        · exact hanti E (hZsub E hE)
      · rintro E (rfl | hE) E' (rfl | hE') hEE'
        · exact absurd rfl hEE'
        · exact hWdisjZ E' hE'
        · exact (hWdisjZ E hE).symm
        · exact hdisj E (hZsub E hE) E' (hZsub E' hE') hEE'
      · rintro E (rfl | hE) E' (rfl | hE') hEE'
        · exact absurd rfl hEE'
        · exact hWcomplZ E' hE'
        · exact complete_symm (hWcomplZ E hE)
        · exact hcompl E (hZsub E hE) E' (hZsub E' hE') hEE'
    have hUnion : ⋃₀ (insert W 𝒵) = insert v (⋃₀ 𝒳) := by
      apply Set.Subset.antisymm
      · rintro z ⟨E, hE, hzE⟩
        rcases hE with rfl | hE
        · rcases (hmemW z).mp hzE with ⟨E', hEY, hzE'⟩ | hzv
          · exact Or.inr ⟨E', hYsub E' hEY, hzE'⟩
          · exact Or.inl hzv
        · exact Or.inr ⟨E, hZsub E hE, hzE⟩
      · rintro z (hzv | ⟨E, hE, hzE⟩)
        · exact ⟨W, Set.mem_insert _ _, (hmemW z).mpr (Or.inr hzv)⟩
        · by_cases hv : VertexComplete G v E
          · exact ⟨E, Set.mem_insert_of_mem _ ((hmemZ E).mpr ⟨hE, hv⟩), hzE⟩
          · exact ⟨W, Set.mem_insert _ _,
              (hmemW z).mpr (Or.inl ⟨E, (hmemY E).mpr ⟨hE, hv⟩, hzE⟩)⟩
    have hle := hmax (insert W 𝒵) hgood'
    rw [hUnion, Set.ncard_insert_of_notMem hvU (Set.toFinite _)] at hle
    omega


end SPGT

end Workspace.Statements.S24
