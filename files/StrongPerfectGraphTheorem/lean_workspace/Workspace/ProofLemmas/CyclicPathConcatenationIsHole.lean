import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathGlue

/-!
# Gluing a cyclic family of induced paths into a hole

Pure list/hole infrastructure, with no strip-system content.  `PrismBasics` and `PathGlue`
close a *single* path into a hole through one or two extra vertices; this module does the
general cyclic case: `m ≥ 3` pairwise vertex-disjoint induced paths, laid end to end round a
cycle, with exactly one edge between each cyclically consecutive pair (last vertex of one to
first vertex of the next) and no edge at all between non-consecutive pairs, concatenate to a
hole.

This is the *"the union of `V(R)` and all the `V(R_xy)`'s induces a cycle in `G`"* step of the
printed proof of statement 8.1.  Its three hypotheses are exactly what the strip-system axioms
supply: axiom 2 gives the pairwise disjointness (`StripSystemBasics.strip_disjoint`), axiom 6
the consecutive-link `↔`, axiom 5 the non-consecutive anticompleteness.

The proof splits the cycle at the first block: the remaining `m − 1` blocks form a *linear*
chain, which `chain_isPathFrom` folds into a single induced path by iterating
`PathGlue.glue_path`; then `PathGlue.glue_hole` closes that path against the first block.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.CyclicPathConcatenationIsHole

open Workspace.Types.Core Workspace.Types.Core.SPGT

/-! ## A linear chain of paths concatenates to a path -/

/-- A *linear* family of induced paths, pairwise vertex-disjoint, in which the only edges
between consecutive blocks join the last vertex of one to the first vertex of the next and
there are no edges at all between non-consecutive blocks, concatenates to an induced path. -/
private theorem chain_isPathFrom {V : Type*} (G : SimpleGraph V) :
    ∀ (Q : List (List V)) (s t : ℕ → V), Q ≠ [] →
    (∀ (i : ℕ) (hi : i < Q.length), IsPathFrom G (Q[i]'hi) (s i) (t i)) →
    (∀ (i j : ℕ) (hi : i < Q.length) (hj : j < Q.length), i ≠ j →
        ∀ x ∈ Q[i]'hi, x ∉ Q[j]'hj) →
    (∀ (i : ℕ) (hi : i < Q.length) (hi1 : i + 1 < Q.length),
        ∀ x ∈ Q[i]'hi, ∀ y ∈ Q[i + 1]'hi1, (G.Adj x y ↔ (x = t i ∧ y = s (i + 1)))) →
    (∀ (i j : ℕ) (hi : i < Q.length) (hj : j < Q.length), i + 1 < j →
        ∀ x ∈ Q[i]'hi, ∀ y ∈ Q[j]'hj, ¬ G.Adj x y) →
    IsPathFrom G (Q.flatMap id) (s 0) (t (Q.length - 1)) := by
  intro Q
  induction Q with
  | nil => intro s t hne _ _ _ _; exact absurd rfl hne
  | cons a Q' ih =>
    intro s t _ hpath hdisj hlink hfar
    by_cases hQ' : Q' = []
    · subst hQ'
      have h0 : IsPathFrom G a (s 0) (t 0) := hpath 0 (by simp)
      simpa using h0
    · have hQpos : 0 < Q'.length := by
        cases Q' with
        | nil => exact absurd rfl hQ'
        | cons _ _ => simp
      have hpath' : ∀ (i : ℕ) (hi : i < Q'.length),
          IsPathFrom G (Q'[i]'hi) (s (i + 1)) (t (i + 1)) := by
        intro i hi
        exact hpath (i + 1) (by simp only [List.length_cons]; omega)
      have hdisj' : ∀ (i j : ℕ) (hi : i < Q'.length) (hj : j < Q'.length), i ≠ j →
          ∀ x ∈ Q'[i]'hi, x ∉ Q'[j]'hj := by
        intro i j hi hj hij x hx
        exact hdisj (i + 1) (j + 1) (by simp only [List.length_cons]; omega)
          (by simp only [List.length_cons]; omega) (by omega) x hx
      have hlink' : ∀ (i : ℕ) (hi : i < Q'.length) (hi1 : i + 1 < Q'.length),
          ∀ x ∈ Q'[i]'hi, ∀ y ∈ Q'[i + 1]'hi1,
            (G.Adj x y ↔ (x = t (i + 1) ∧ y = s (i + 1 + 1))) := by
        intro i hi hi1 x hx y hy
        exact hlink (i + 1) (by simp only [List.length_cons]; omega)
          (by simp only [List.length_cons]; omega) x hx y hy
      have hfar' : ∀ (i j : ℕ) (hi : i < Q'.length) (hj : j < Q'.length), i + 1 < j →
          ∀ x ∈ Q'[i]'hi, ∀ y ∈ Q'[j]'hj, ¬ G.Adj x y := by
        intro i j hi hj hij x hx y hy
        exact hfar (i + 1) (j + 1) (by simp only [List.length_cons]; omega)
          (by simp only [List.length_cons]; omega) (by omega) x hx y hy
      have hQlen : Q'.length - 1 + 1 = Q'.length := by omega
      have IH : IsPathFrom G (Q'.flatMap id) (s 1) (t Q'.length) := by
        have h := ih (fun i => s (i + 1)) (fun i => t (i + 1)) hQ' hpath' hdisj' hlink' hfar'
        simp only [hQlen] at h
        exact h
      have ha : IsPathFrom G a (s 0) (t 0) := hpath 0 (by simp)
      -- membership in the flattened tail
      have hmemQ' : ∀ y : V, y ∈ Q'.flatMap id → ∃ j, ∃ hj : j < Q'.length, y ∈ Q'[j]'hj := by
        intro y hy
        rw [List.mem_flatMap] at hy
        obtain ⟨l, hl, hyl⟩ := hy
        rw [List.mem_iff_getElem] at hl
        obtain ⟨j, hj, rfl⟩ := hl
        exact ⟨j, hj, hyl⟩
      have hs1 : s 1 ∈ Q'[0]'hQpos := by
        have h := hpath' 0 hQpos
        exact List.mem_of_mem_head? (by rw [h.2.1]; rfl)
      have hdisjG : ∀ x ∈ a, x ∉ Q'.flatMap id := by
        intro x hx hmem
        obtain ⟨j, hj, hxj⟩ := hmemQ' x hmem
        exact hdisj 0 (j + 1) (by simp) (by simp only [List.length_cons]; omega)
          (by omega) x hx hxj
      have hcross : ∀ x ∈ a, ∀ y ∈ Q'.flatMap id, (G.Adj x y ↔ (x = t 0 ∧ y = s 1)) := by
        intro x hx y hy
        obtain ⟨j, hj, hyj⟩ := hmemQ' y hy
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · exact hlink 0 (by simp) (by simp only [List.length_cons]; omega) x hx y hyj
        · constructor
          · intro hadj
            exact absurd hadj
              (hfar 0 (j + 1) (by simp) (by simp only [List.length_cons]; omega)
                (by omega) x hx y hyj)
          · rintro ⟨-, rfl⟩
            exact absurd hyj (hdisj' 0 j hQpos hj (by omega) (s 1) hs1)
      have hglue := PathGlue.glue_path ha IH hdisjG hcross
      rw [List.flatMap_cons]
      simpa using hglue

/-! ## The cyclic version: a hole -/

/-- **The cyclic concatenation lemma.**  A cyclic family `P₀, …, P_{m-1}` (`m ≥ 3`) of induced
paths of `G` with ends `sᵢ`, `tᵢ`, pairwise vertex-disjoint, such that the only edge between
`V(Pᵢ)` and `V(P_{i+1})` is `tᵢ s_{i+1}` (indices mod `m`) and there are no edges at all between
non-cyclically-consecutive members, concatenates to a hole of `G`.

This is the *"the union of `V(R)` and all the `V(R_xy)`'s induces a cycle in `G`"* step of the
printed proof of 8.1. -/
theorem isHoleList_flatMap_of_cyclic {V : Type*} (G : SimpleGraph V)
    (P : List (List V)) (s t : ℕ → V)
    (hm : 3 ≤ P.length)
    (hpath : ∀ (i : ℕ) (hi : i < P.length), IsPathFrom G (P[i]'hi) (s i) (t i))
    (hdisj : ∀ (i j : ℕ) (hi : i < P.length) (hj : j < P.length), i ≠ j →
        ∀ x ∈ P[i]'hi, x ∉ P[j]'hj)
    (hlink : ∀ (i : ℕ) (hi : i < P.length),
        ∀ x ∈ P[i]'hi, ∀ y ∈ P[(i + 1) % P.length]'(Nat.mod_lt _ (by omega)),
          (G.Adj x y ↔ (x = t i ∧ y = s ((i + 1) % P.length))))
    (hfar : ∀ (i j : ℕ) (hi : i < P.length) (hj : j < P.length), i ≠ j →
        j ≠ (i + 1) % P.length → i ≠ (j + 1) % P.length →
        ∀ x ∈ P[i]'hi, ∀ y ∈ P[j]'hj, ¬ G.Adj x y)
    (h4 : 4 ≤ (P.flatMap id).length) :
    IsHoleList G (P.flatMap id) := by
  -- Restate `hlink` in a form where the second index is a free variable.
  have hlink' : ∀ (i j : ℕ) (hi : i < P.length) (hj : j < P.length), j = (i + 1) % P.length →
      ∀ x ∈ P[i]'hi, ∀ y ∈ P[j]'hj, (G.Adj x y ↔ (x = t i ∧ y = s j)) := by
    intro i j hi hj hji x hx y hy
    subst hji
    exact hlink i hi x hx y hy
  -- Split off the first block.
  obtain ⟨P₀, Q, rfl⟩ : ∃ P₀ Q, P = P₀ :: Q := by
    cases P with
    | nil => simp at hm
    | cons a l => exact ⟨a, l, rfl⟩
  have hlenP : (P₀ :: Q).length = Q.length + 1 := by simp
  have hQ2 : 2 ≤ Q.length := by simp only [List.length_cons] at hm; omega
  have hQne : Q ≠ [] := by
    intro h; rw [h] at hQ2; simp at hQ2
  -- move a membership fact from `Q[j]` to the ambient list at any index equal to `j+1`
  have hmemP : ∀ (j : ℕ) (hj : j < Q.length) (y : V), y ∈ Q[j]'hj →
      ∀ (k : ℕ) (hk : k < (P₀ :: Q).length), k = j + 1 → y ∈ (P₀ :: Q)[k]'hk := by
    intro j hj y hy k hk hkj
    subst hkj
    exact hy
  -- the tail is a linear chain
  have hpath' : ∀ (i : ℕ) (hi : i < Q.length),
      IsPathFrom G (Q[i]'hi) (s (i + 1)) (t (i + 1)) := by
    intro i hi
    exact hpath (i + 1) (by simp only [List.length_cons]; omega)
  have hdisj' : ∀ (i j : ℕ) (hi : i < Q.length) (hj : j < Q.length), i ≠ j →
      ∀ x ∈ Q[i]'hi, x ∉ Q[j]'hj := by
    intro i j hi hj hij x hx
    exact hdisj (i + 1) (j + 1) (by simp only [List.length_cons]; omega)
      (by simp only [List.length_cons]; omega) (by omega) x hx
  have hlinkQ : ∀ (i : ℕ) (hi : i < Q.length) (hi1 : i + 1 < Q.length),
      ∀ x ∈ Q[i]'hi, ∀ y ∈ Q[i + 1]'hi1,
        (G.Adj x y ↔ (x = t (i + 1) ∧ y = s (i + 1 + 1))) := by
    intro i hi hi1 x hx y hy
    have hxP : x ∈ (P₀ :: Q)[i + 1]'(by simp only [List.length_cons]; omega) := hx
    have hyP : y ∈ (P₀ :: Q)[i + 1 + 1]'(by simp only [List.length_cons]; omega) := hy
    refine hlink' (i + 1) (i + 1 + 1) _ _ ?_ x hxP y hyP
    rw [Nat.mod_eq_of_lt (by simp only [List.length_cons]; omega)]
  have hfarQ : ∀ (i j : ℕ) (hi : i < Q.length) (hj : j < Q.length), i + 1 < j →
      ∀ x ∈ Q[i]'hi, ∀ y ∈ Q[j]'hj, ¬ G.Adj x y := by
    intro i j hi hj hij x hx y hy
    have hxP : x ∈ (P₀ :: Q)[i + 1]'(by simp only [List.length_cons]; omega) := hx
    have hyP : y ∈ (P₀ :: Q)[j + 1]'(by simp only [List.length_cons]; omega) := hy
    have hmod1 : (i + 1 + 1) % (P₀ :: Q).length = i + 1 + 1 := by
      rw [Nat.mod_eq_of_lt (by simp only [List.length_cons]; omega)]
    have hmod2 : (j + 1 + 1) % (P₀ :: Q).length = 0 ∨
        (j + 1 + 1) % (P₀ :: Q).length = j + 1 + 1 := by
      rcases eq_or_lt_of_le (show j + 1 + 1 ≤ (P₀ :: Q).length by
        simp only [List.length_cons]; omega) with h | h
      · left; rw [h]; exact Nat.mod_self _
      · right; exact Nat.mod_eq_of_lt h
    refine hfar (i + 1) (j + 1) _ _ (by omega) (by omega) (by omega) x hxP y hyP
  have hQlen : Q.length - 1 + 1 = Q.length := by omega
  have hchain : IsPathFrom G (Q.flatMap id) (s 1) (t Q.length) := by
    have h := chain_isPathFrom G Q (fun i => s (i + 1)) (fun i => t (i + 1)) hQne
      hpath' hdisj' hlinkQ hfarQ
    simp only [hQlen] at h
    exact h
  have hP₀ : IsPathFrom G P₀ (s 0) (t 0) := hpath 0 (by simp)
  -- the two distinguished vertices of the last / second block
  have hs1 : s 1 ∈ (P₀ :: Q)[1]'(by simp only [List.length_cons]; omega) := by
    have h := hpath 1 (by simp only [List.length_cons]; omega)
    exact List.mem_of_mem_head? (by rw [h.2.1]; rfl)
  have htQ : t Q.length ∈ (P₀ :: Q)[Q.length]'(by simp only [List.length_cons]; omega) := by
    have h := hpath Q.length (by simp only [List.length_cons]; omega)
    exact List.mem_of_mem_getLast? (by rw [h.2.2]; rfl)
  have hmemQ : ∀ y : V, y ∈ Q.flatMap id → ∃ j, ∃ hj : j < Q.length, y ∈ Q[j]'hj := by
    intro y hy
    rw [List.mem_flatMap] at hy
    obtain ⟨l, hl, hyl⟩ := hy
    rw [List.mem_iff_getElem] at hl
    obtain ⟨j, hj, rfl⟩ := hl
    exact ⟨j, hj, hyl⟩
  have hdisjPQ : ∀ x ∈ P₀, x ∉ Q.flatMap id := by
    intro x hx hmem
    obtain ⟨j, hj, hxj⟩ := hmemQ x hmem
    exact hdisj 0 (j + 1) (by simp) (by simp only [List.length_cons]; omega)
      (by omega) x hx hxj
  have hcross : ∀ x ∈ P₀, ∀ y ∈ Q.flatMap id,
      (G.Adj x y ↔ (x = t 0 ∧ y = s 1) ∨ (x = s 0 ∧ y = t Q.length)) := by
    intro x hx y hy
    obtain ⟨j, hj, hyj⟩ := hmemQ y hy
    have hxP : x ∈ (P₀ :: Q)[0]'(by simp only [List.length_cons]; omega) := hx
    have hyP : y ∈ (P₀ :: Q)[j + 1]'(by simp only [List.length_cons]; omega) :=
      hmemP j hj y hyj (j + 1) _ rfl
    by_cases hj0 : j = 0
    · -- `y` lies in the second block: the printed link `t₀ s₁`
      subst hj0
      have hyP1 : y ∈ (P₀ :: Q)[1]'(by simp only [List.length_cons]; omega) := hyP
      have hlk := hlink' 0 1 (by simp only [List.length_cons]; omega)
        (by simp only [List.length_cons]; omega)
        (by rw [Nat.mod_eq_of_lt (by simp only [List.length_cons]; omega)]) x hxP y hyP1
      have hne2 : ¬ (x = s 0 ∧ y = t Q.length) := by
        rintro ⟨-, rfl⟩
        exact hdisj Q.length 1 (by simp only [List.length_cons]; omega)
          (by simp only [List.length_cons]; omega) (by omega) _ htQ hyP1
      rw [hlk]; tauto
    · by_cases hjl : j + 1 = Q.length
      · -- `y` lies in the last block: the printed wrap-around link `t_{m-1} s₀`
        have hyPl : y ∈ (P₀ :: Q)[Q.length]'(by simp only [List.length_cons]; omega) :=
          hmemP j hj y hyj Q.length _ (by omega)
        have hlk := hlink' Q.length 0 (by simp only [List.length_cons]; omega)
          (by simp only [List.length_cons]; omega)
          (by rw [hlenP, Nat.mod_self]) y hyPl x hxP
        have hne1 : ¬ (x = t 0 ∧ y = s 1) := by
          rintro ⟨-, rfl⟩
          exact hdisj 1 Q.length (by simp only [List.length_cons]; omega)
            (by simp only [List.length_cons]; omega) (by omega) _ hs1 hyPl
        rw [SimpleGraph.adj_comm, hlk]
        constructor
        · rintro ⟨h1, h2⟩; exact Or.inr ⟨h2, h1⟩
        · rintro (h | ⟨h1, h2⟩)
          · exact absurd h hne1
          · exact ⟨h2, h1⟩
      · -- `y` lies in a non-consecutive block
        have hmod2 : (j + 1 + 1) % (P₀ :: Q).length = j + 1 + 1 := by
          rw [Nat.mod_eq_of_lt (by simp only [List.length_cons]; omega)]
        have hnadj : ¬ G.Adj x y := by
          refine hfar 0 (j + 1) (by simp only [List.length_cons]; omega)
            (by simp only [List.length_cons]; omega) (by omega) ?_ (by omega) x hxP y hyP
          rw [Nat.mod_eq_of_lt (by simp only [List.length_cons]; omega)]
          omega
        have hne1 : ¬ (x = t 0 ∧ y = s 1) := by
          rintro ⟨-, rfl⟩
          exact hdisj 1 (j + 1) (by simp only [List.length_cons]; omega)
            (by simp only [List.length_cons]; omega) (by omega) _ hs1 hyP
        have hne2 : ¬ (x = s 0 ∧ y = t Q.length) := by
          rintro ⟨-, rfl⟩
          exact hdisj Q.length (j + 1) (by simp only [List.length_cons]; omega)
            (by simp only [List.length_cons]; omega) (by omega) _ htQ hyP
        constructor
        · intro h; exact absurd h hnadj
        · rintro (h | h)
          · exact absurd h hne1
          · exact absurd h hne2
  have hlen4 : 4 ≤ P₀.length + (Q.flatMap id).length := by
    simpa [List.flatMap_cons] using h4
  have hhole := PathGlue.glue_hole hP₀ hchain hdisjPQ hcross hlen4
  rw [List.flatMap_cons]
  simpa using hhole

/-- The length of the hole built by `isHoleList_flatMap_of_cyclic` is the sum of the sizes of
the blocks — i.e. `∑ (pathLength Pᵢ + 1)`, which is what the parity computation of 8.1 needs. -/
theorem holeLength_flatMap {V : Type*} (P : List (List V)) :
    holeLength (P.flatMap id) = (P.map List.length).sum := by
  simp [holeLength]

end Workspace.ProofLemmas.CyclicPathConcatenationIsHole
