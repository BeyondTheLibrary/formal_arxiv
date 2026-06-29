import Mathlib

/-!
# Coordinate-wise median predicate

This file defines the predicate `IsCoordinateMedian` saying that a vector
`m : Fin d → ℝ` is a coordinate-wise median of an instance
`P : Fin n → Fin d → ℝ`, in the sense that for every coordinate `j`,
both `#{i : P i j < m j}` and `#{i : P i j > m j}` are at most `n / 2`
(natural-number integer division).

The existence theorem `exists_coordinateMedian` shows that every instance
admits a coordinate-wise median; we construct one by sorting each
coordinate and taking the `n / 2`-th order statistic.
-/

namespace Workspace.Types.CoordinateMedian

open Finset

/-- A vector `m : Fin d → ℝ` is a *coordinate-wise median* of the instance
`P : Fin n → Fin d → ℝ` if for every coordinate `j`, both the number of
indices `i` with `P i j < m j` and the number of indices with
`P i j > m j` are at most `n / 2` (natural-number integer division).

When `n` is even, this gives `n / 2` on each side; when `n` is odd, this
gives `⌊n/2⌋ = (n - 1) / 2` on each side. The predicate models arbitrary
tie-breaking: many `m` will satisfy it for typical instances. -/
def IsCoordinateMedian {n d : ℕ} (m : Fin d → ℝ) (P : Fin n → Fin d → ℝ) : Prop :=
  ∀ j : Fin d,
    (Finset.univ.filter (fun i : Fin n => P i j < m j)).card ≤ n / 2 ∧
    (Finset.univ.filter (fun i : Fin n => P i j > m j)).card ≤ n / 2

/-- Helper lemma: for a monotone function `g : Fin n → ℝ`, choosing the
`n / 2`-th order statistic gives both upper bounds. -/
private lemma monotone_median_bounds {n : ℕ} (g : Fin n → ℝ) (hg : Monotone g)
    (hn : 0 < n) :
    let k : Fin n := ⟨n / 2, Nat.div_lt_of_lt_mul (by
      have : n ≤ n * 2 := Nat.le_mul_of_pos_right _ (by decide)
      omega)⟩
    (Finset.univ.filter (fun i : Fin n => g i < g k)).card ≤ n / 2 ∧
    (Finset.univ.filter (fun i : Fin n => g i > g k)).card ≤ n / 2 := by
  intro k
  refine ⟨?_, ?_⟩
  · -- {i : g i < g k} ⊆ {i : i.val < n/2}
    have hsub : (Finset.univ.filter (fun i : Fin n => g i < g k)) ⊆
        (Finset.univ.filter (fun i : Fin n => i.val < n / 2)) := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      by_contra hi'
      have hi'' : n / 2 ≤ i.val := Nat.le_of_not_lt hi'
      -- i.val ≥ n/2 = k.val, so by monotone g i ≥ g k, contradicting g i < g k
      have : k ≤ i := by
        change k.val ≤ i.val
        exact hi''
      have := hg this
      linarith
    refine le_trans (card_le_card hsub) ?_
    -- card of {i : i.val < n/2} is exactly min(n, n/2) = n/2 (since n/2 ≤ n)
    have : (Finset.univ.filter (fun i : Fin n => i.val < n / 2)).card = n / 2 := by
      rw [show (Finset.univ.filter (fun i : Fin n => i.val < n / 2)) =
        (Finset.range (n / 2)).attachFin (fun m hm => by
          simp at hm
          exact lt_of_lt_of_le hm (Nat.div_le_self n 2)) from ?_]
      · simp
      · ext i
        simp [Finset.mem_attachFin]
    omega
  · -- {i : g i > g k} ⊆ {i : i.val > n/2}, which has cardinality n - n/2 - 1 ≤ n/2
    have hsub : (Finset.univ.filter (fun i : Fin n => g i > g k)) ⊆
        (Finset.univ.filter (fun i : Fin n => i.val > n / 2)) := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      by_contra hi'
      have hi'' : i.val ≤ n / 2 := Nat.le_of_not_lt hi'
      have : i ≤ k := by
        change i.val ≤ k.val
        exact hi''
      have := hg this
      linarith
    refine le_trans (card_le_card hsub) ?_
    -- card of {i : i.val > n/2} = n - (n/2 + 1)
    have hle : (Finset.univ.filter (fun i : Fin n => i.val ≤ n / 2)).card = n / 2 + 1 := by
      rw [show (Finset.univ.filter (fun i : Fin n => i.val ≤ n / 2)) =
        (Finset.range (n / 2 + 1)).attachFin (fun m hm => by
          simp at hm
          omega) from ?_]
      · simp
      · ext i
        simp [Finset.mem_attachFin]
    have hsum :
        (Finset.univ.filter (fun i : Fin n => i.val > n / 2)).card +
        (Finset.univ.filter (fun i : Fin n => i.val ≤ n / 2)).card = n := by
      rw [← card_union_of_disjoint, show
        (Finset.univ.filter (fun i : Fin n => i.val > n / 2)) ∪
        (Finset.univ.filter (fun i : Fin n => i.val ≤ n / 2)) = Finset.univ from ?_]
      · simp
      · ext i; simp; omega
      · rw [disjoint_filter]
        intros; omega
    omega

/-- Every instance `P : Fin n → Fin d → ℝ` admits a coordinate-wise
median. We construct one by sorting each coordinate independently and
taking the `n / 2`-th order statistic. -/
theorem exists_coordinateMedian (n d : ℕ) (P : Fin n → Fin d → ℝ) :
    ∃ m, IsCoordinateMedian m P := by
  classical
  by_cases hn : n = 0
  · -- vacuous: all filters over Fin 0 have cardinality 0
    refine ⟨fun _ => 0, ?_⟩
    intro j
    subst hn
    refine ⟨?_, ?_⟩ <;> simp
  -- n ≥ 1
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  -- For each coordinate j, define m j as the n/2-th value of the sorted j-th column.
  refine ⟨fun j => P (Tuple.sort (fun i => P i j) ⟨n / 2,
    Nat.div_lt_of_lt_mul (by
      have hh : n ≤ n * 2 := Nat.le_mul_of_pos_right _ (by decide)
      omega)⟩) j, ?_⟩
  intro j
  -- Let f i = P i j; let σ = Tuple.sort f. Then g := f ∘ σ is monotone.
  set f : Fin n → ℝ := fun i => P i j with hf
  set σ : Equiv.Perm (Fin n) := Tuple.sort f with hσ
  set g : Fin n → ℝ := f ∘ σ with hg_def
  have hg_mono : Monotone g := Tuple.monotone_sort f
  set k : Fin n := ⟨n / 2, Nat.div_lt_of_lt_mul (by
    have hh : n ≤ n * 2 := Nat.le_mul_of_pos_right _ (by decide)
    omega)⟩ with hk_def
  -- The chosen median is f (σ k) = g k
  have hm_eq : (fun j' => P (Tuple.sort (fun i => P i j') ⟨n / 2,
      Nat.div_lt_of_lt_mul (by
        have hh : n ≤ n * 2 := Nat.le_mul_of_pos_right _ (by decide)
        omega)⟩) j') j = g k := by
    simp [hg_def, hf, hσ, hk_def]
  rw [hm_eq]
  -- Bounds for g via monotone_median_bounds
  obtain ⟨hlt, hgt⟩ := monotone_median_bounds g hg_mono hn'
  -- Translate cardinality of {i : f i < g k} to {i : g i < g k} via the bijection σ
  refine ⟨?_, ?_⟩
  · -- card {i : P i j < g k} ≤ n / 2
    have heq : (Finset.univ.filter (fun i : Fin n => P i j < g k)).card =
        (Finset.univ.filter (fun i : Fin n => g i < g k)).card := by
      apply Finset.card_bij (fun i _ => σ.symm i)
      · intro i hi
        simp only [mem_filter, mem_univ, true_and] at hi ⊢
        show f (σ (σ.symm i)) < g k
        rw [σ.apply_symm_apply]
        exact hi
      · intros a _ b _ hab
        exact σ.symm.injective hab
      · intro i hi
        simp only [mem_filter, mem_univ, true_and] at hi
        refine ⟨σ i, ?_, ?_⟩
        · simp only [mem_filter, mem_univ, true_and]
          show f (σ i) < g k
          exact hi
        · simp
    rw [heq]
    exact hlt
  · -- card {i : P i j > g k} ≤ n / 2
    have heq : (Finset.univ.filter (fun i : Fin n => P i j > g k)).card =
        (Finset.univ.filter (fun i : Fin n => g i > g k)).card := by
      apply Finset.card_bij (fun i _ => σ.symm i)
      · intro i hi
        simp only [mem_filter, mem_univ, true_and] at hi ⊢
        show f (σ (σ.symm i)) > g k
        rw [σ.apply_symm_apply]
        exact hi
      · intros a _ b _ hab
        exact σ.symm.injective hab
      · intro i hi
        simp only [mem_filter, mem_univ, true_and] at hi
        refine ⟨σ i, ?_, ?_⟩
        · simp only [mem_filter, mem_univ, true_and]
          show f (σ i) > g k
          exact hi
        · simp
    rw [heq]
    exact hgt

/-- When `d = 0`, every vector `m : Fin 0 → ℝ` is a coordinate-wise median of
every placement `P : Fin n → Fin 0 → ℝ`. The predicate's universal quantifier
over `Fin 0` is vacuous. -/
theorem isCoordinateMedian_dim_zero {n : ℕ} (m : Fin 0 → ℝ) (P : Fin n → Fin 0 → ℝ) :
    IsCoordinateMedian m P := by
  intro j
  exact j.elim0

/-- When `n = 1`, `IsCoordinateMedian m P` is equivalent to `m = P 0`: with a
single placement, the median predicate forces `m` to coincide with that
placement on every coordinate. -/
theorem isCoordinateMedian_unique_singleton {d : ℕ} (m : Fin d → ℝ) (P : Fin 1 → Fin d → ℝ) :
    IsCoordinateMedian m P ↔ m = P 0 := by
  classical
  constructor
  · intro h
    funext j
    obtain ⟨hlt, hgt⟩ := h j
    -- 1 / 2 = 0, so both filtered sets must be empty.
    have hlt0 : (Finset.univ.filter (fun i : Fin 1 => P i j < m j)).card = 0 := by
      have : (1 : ℕ) / 2 = 0 := rfl
      omega
    have hgt0 : (Finset.univ.filter (fun i : Fin 1 => P i j > m j)).card = 0 := by
      have : (1 : ℕ) / 2 = 0 := rfl
      omega
    have hlt_empty : ¬ (P 0 j < m j) := by
      intro hcontr
      have : (0 : Fin 1) ∈ Finset.univ.filter (fun i : Fin 1 => P i j < m j) := by
        simp [hcontr]
      have : 0 < (Finset.univ.filter (fun i : Fin 1 => P i j < m j)).card :=
        Finset.card_pos.mpr ⟨0, this⟩
      omega
    have hgt_empty : ¬ (P 0 j > m j) := by
      intro hcontr
      have : (0 : Fin 1) ∈ Finset.univ.filter (fun i : Fin 1 => P i j > m j) := by
        simp [hcontr]
      have : 0 < (Finset.univ.filter (fun i : Fin 1 => P i j > m j)).card :=
        Finset.card_pos.mpr ⟨0, this⟩
      omega
    -- Trichotomy on ℝ: not <, not >, so equal. Statement is `m j = P 0 j`.
    have : P 0 j = m j := le_antisymm (not_lt.mp hgt_empty) (not_lt.mp hlt_empty)
    exact this.symm
  · intro hm
    intro j
    -- Under `m = P 0`, `m j = P 0 j`, so neither strict inequality can hold for
    -- the only index `0 : Fin 1`.
    have hmj : m j = P 0 j := by rw [hm]
    have hlt_empty :
        (Finset.univ.filter (fun i : Fin 1 => P i j < m j)) = ∅ := by
      ext i
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      have hi0 : i = 0 := Subsingleton.elim _ _
      rw [hi0, hmj]
      exact lt_irrefl _
    have hgt_empty :
        (Finset.univ.filter (fun i : Fin 1 => P i j > m j)) = ∅ := by
      ext i
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      have hi0 : i = 0 := Subsingleton.elim _ _
      rw [hi0, hmj]
      exact lt_irrefl _
    refine ⟨?_, ?_⟩
    · rw [hlt_empty]; simp
    · rw [hgt_empty]; simp

end Workspace.Types.CoordinateMedian
