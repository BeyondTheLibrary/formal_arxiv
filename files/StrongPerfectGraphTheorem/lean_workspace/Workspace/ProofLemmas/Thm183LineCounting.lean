import Mathlib

/-!
# 18.3, the final counting paragraph, as pure arithmetic

This module contains **no graph theory**: it is the abstract skeleton of the counting
paragraph that closes the proof of statement **18.3** of Chudnovsky–Robertson–Seymour–Thomas.

Think of `0, 1, …, N-1` as the vertices of a path, and of `c k` as "the `k`-th vertex is
`Y`-complete".  A *T-point* is an index which is `0`, or `N-1`, or satisfies `c`; a *line* is
a pair of consecutive T-points `(i, j)`, of length `j - i`.  The three hypotheses are the
paper's three facts about lines:

* `hEven` — a line of length `≥ 2` both of whose ends satisfy `c` has even length;
* `hOddL` — a line of length `≥ 2` starting at `0`, when `¬ c 0`, has odd length;
* `hOddR` — a line of length `≥ 2` ending at `N-1`, when `¬ c (N-1)`, has odd length.

Lines of length `1` are odd for free.  Since the whole path has even length (`hNeven`), summing
the lengths of the lines gives: the number of `Y`-complete edges has the same parity as the
number of ends of the path that are `Y`-complete.

The proof is an induction from the right along the T-points: writing

* `yFrom i` for the number of `Y`-complete edges inside `[i, N-1]`,
* `zL i`, `zR i` for the two boundary corrections,

one shows `(N - 1 - i) % 2 = (yFrom i + zL i + zR i) % 2` for every T-point `i`, by strong
induction on `N - 1 - i`, and then specialises to `i = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm183LineCounting

/-- The number of `Y`-complete edges `{k, k+1}` with `i ≤ k < N - 1`. -/
private def yFrom (N : ℕ) (c : ℕ → Prop) [DecidablePred c] (i : ℕ) : ℕ :=
  ((Finset.Ico i (N - 1)).filter (fun k => c k ∧ c (k + 1))).card

/-- Left boundary correction: `1` exactly when `i` is the left end of the path and that end
is not `Y`-complete. -/
private def zL (c : ℕ → Prop) [DecidablePred c] (i : ℕ) : ℕ :=
  if i = 0 ∧ ¬ c 0 then 1 else 0

/-- Right boundary correction: `1` exactly when `i` is not itself the right end of the path
and that right end is not `Y`-complete. -/
private def zR (N : ℕ) (c : ℕ → Prop) [DecidablePred c] (i : ℕ) : ℕ :=
  if i = N - 1 then 0 else if c (N - 1) then 0 else 1

/-- Splitting the edge count at an intermediate index. -/
private lemma split_count (N : ℕ) (c : ℕ → Prop) [DecidablePred c] {i j : ℕ}
    (hij : i ≤ j) (hjN : j ≤ N - 1) :
    yFrom N c i
      = ((Finset.Ico i j).filter (fun k => c k ∧ c (k + 1))).card + yFrom N c j := by
  unfold yFrom
  rw [← Finset.Ico_union_Ico_eq_Ico hij hjN, Finset.filter_union,
    Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive i j (N - 1)))]

/-- Inside a line there is at most one `Y`-complete edge, and there is one exactly when the
line has length `1` and both its ends are `Y`-complete. -/
private lemma near_count (c : ℕ → Prop) [DecidablePred c] {i j : ℕ} (hij : i < j)
    (hnone : ∀ k, i < k → k < j → ¬ c k) :
    ((Finset.Ico i j).filter (fun k => c k ∧ c (k + 1))).card
      = if j = i + 1 ∧ c i ∧ c j then 1 else 0 := by
  split_ifs with h
  · obtain ⟨hj, hci, hcj⟩ := h
    rw [hj] at hcj ⊢
    simp [Nat.Ico_succ_singleton, Finset.filter_singleton, hci, hcj]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k hk hck
    rw [Finset.mem_Ico] at hk
    by_cases hki : i < k
    · exact hnone k hki hk.2 hck.1
    · have hke : k = i := by omega
      rw [hke] at hck
      have hj1 : j = i + 1 := by
        by_contra hne
        exact hnone (i + 1) (by omega) (by omega) hck.2
      exact h ⟨hj1, hck.1, by rw [hj1]; exact hck.2⟩

/-- The induction from the right along the T-points.  The extra argument `m` is fuel: it lets
the induction be an ordinary `Nat` induction on an upper bound for `N - 1 - i`. -/
private lemma key (N : ℕ) (c : ℕ → Prop) [DecidablePred c] (hN : 5 ≤ N)
    (h2 : 2 ≤ ((Finset.range N).filter c).card)
    (hEven : ∀ i j : ℕ, i + 2 ≤ j → j ≤ N - 1 →
        (∀ k, i < k → k < j → ¬ c k) → c i → c j → Even (j - i))
    (hOddL : ∀ j : ℕ, 2 ≤ j → j ≤ N - 1 →
        (∀ k, 0 < k → k < j → ¬ c k) → ¬ c 0 → c j → Odd j)
    (hOddR : ∀ i : ℕ, 0 < i → i + 2 ≤ N - 1 →
        (∀ k, i < k → k < N - 1 → ¬ c k) → c i → ¬ c (N - 1) → Odd (N - 1 - i)) :
    ∀ m i : ℕ, N - 1 - i ≤ m → i ≤ N - 1 → (i = 0 ∨ c i ∨ i = N - 1) →
      (N - 1 - i) % 2 = (yFrom N c i + zL c i + zR N c i) % 2 := by
  -- `c` cannot be concentrated on a single index, by `h2`.
  have hbad : ∀ a : ℕ, (∀ x ∈ (Finset.range N).filter c, x = a) → False := by
    intro a hsub
    have hsub' : ((Finset.range N).filter c) ⊆ {a} := fun x hx =>
      Finset.mem_singleton.mpr (hsub x hx)
    have hcard := Finset.card_le_card hsub'
    rw [Finset.card_singleton] at hcard
    omega
  -- the right endpoint: everything vanishes there.
  have hend : ∀ i : ℕ, i = N - 1 →
      (N - 1 - i) % 2 = (yFrom N c i + zL c i + zR N c i) % 2 := by
    intro i hi
    subst hi
    have h1 : yFrom N c (N - 1) = 0 := by
      unfold yFrom
      rw [Finset.Ico_self, Finset.filter_empty, Finset.card_empty]
    have h3 : zL c (N - 1) = 0 := by
      unfold zL
      rw [if_neg (by rintro ⟨h, -⟩; omega)]
    have h4 : zR N c (N - 1) = 0 := by
      unfold zR
      rw [if_pos rfl]
    omega
  intro m
  induction m with
  | zero =>
      intro i hm hi _
      exact hend i (by omega)
  | succ m ih =>
      intro i hm hi hT
      by_cases hiN : i = N - 1
      · exact hend i hiN
      have hilt : i < N - 1 := by omega
      -- `j` := the least T-point strictly greater than `i`
      have hne : ((Finset.Ioc i (N - 1)).filter (fun k => c k ∨ k = N - 1)).Nonempty :=
        ⟨N - 1, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hilt, le_rfl⟩, Or.inr rfl⟩⟩
      obtain ⟨j, hjmem, hjmin⟩ :
          ∃ j, j ∈ ((Finset.Ioc i (N - 1)).filter (fun k => c k ∨ k = N - 1)) ∧
            ∀ k ∈ ((Finset.Ioc i (N - 1)).filter (fun k => c k ∨ k = N - 1)), j ≤ k :=
        ⟨_, Finset.min'_mem _ hne, fun k hk => Finset.min'_le _ k hk⟩
      rw [Finset.mem_filter, Finset.mem_Ioc] at hjmem
      obtain ⟨⟨hij, hjN⟩, hjc⟩ := hjmem
      have hnone : ∀ k, i < k → k < j → ¬ c k := by
        intro k hk1 hk2 hck
        have hle := hjmin k
          (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hk1, by omega⟩, Or.inl hck⟩)
        omega
      have hsplit := split_count N c (le_of_lt hij) hjN
      have hnear := near_count c hij hnone
      have hIH := ih j (by omega) hjN (Or.inr hjc)
      have hzLj : zL c j = 0 := by
        unfold zL
        rw [if_neg (by rintro ⟨h, -⟩; omega)]
      by_cases hjE : j = N - 1
      · -- Case B: the line ends at the right end of the path.
        have hzRj : zR N c j = 0 := by
          unfold zR
          rw [if_pos hjE]
        have hzRi : zR N c i = if c (N - 1) then 0 else 1 := by
          unfold zR
          rw [if_neg hiN]
        by_cases hci : c i
        · have hzLi : zL c i = 0 := by
            unfold zL
            rw [if_neg (by rintro ⟨h1, hn⟩; rw [h1] at hci; exact hn hci)]
          by_cases hcN : c (N - 1)
          · -- B1: both ends of the line are `Y`-complete
            have hcj : c j := by rw [hjE]; exact hcN
            have hzRi' : zR N c i = 0 := by rw [hzRi, if_pos hcN]
            by_cases hj1 : j = i + 1
            · rw [if_pos ⟨hj1, hci, hcj⟩] at hnear
              omega
            · have hev : (j - i) % 2 = 0 :=
                Nat.even_iff.mp (hEven i j (by omega) hjN hnone hci hcj)
              rw [if_neg (by rintro ⟨h1, -, -⟩; exact hj1 h1)] at hnear
              omega
          · -- B2: the right end is not `Y`-complete
            have hncj : ¬ c j := by rw [hjE]; exact hcN
            have hzRi' : zR N c i = 1 := by rw [hzRi, if_neg hcN]
            rw [if_neg (by rintro ⟨-, -, h1⟩; exact hncj h1)] at hnear
            have hodd : (N - 1 - i) % 2 = 1 := by
              by_cases hj1 : j = i + 1
              · omega
              · by_cases hi0 : i = 0
                · -- then `c` holds only at `0`, contradicting `h2`
                  exfalso
                  refine hbad 0 ?_
                  intro x hx
                  rw [Finset.mem_filter, Finset.mem_range] at hx
                  by_contra hx0
                  rcases lt_trichotomy x (N - 1) with h | h | h
                  · exact hnone x (by omega) (by omega) hx.2
                  · exact hcN (by rw [← h]; exact hx.2)
                  · omega
                · exact Nat.odd_iff.mp
                    (hOddR i (by omega) (by omega)
                      (fun k hk1 hk2 => hnone k hk1 (by omega)) hci hcN)
            omega
        · -- `i` is a T-point which is not `Y`-complete, hence `i = 0`; then `c` holds only
          -- at `N - 1`, contradicting `h2`.
          exfalso
          have hi0 : i = 0 := by
            rcases hT with h | h | h
            · exact h
            · exact absurd h hci
            · omega
          have hc0 : ¬ c 0 := by rw [hi0] at hci; exact hci
          refine hbad (N - 1) ?_
          intro x hx
          rw [Finset.mem_filter, Finset.mem_range] at hx
          by_contra hxn
          rcases Nat.eq_zero_or_pos x with h | h
          · exact hc0 (by rw [← h]; exact hx.2)
          · exact hnone x (by omega) (by omega) hx.2
      · -- Case A: the line ends strictly before the right end, so its right end satisfies `c`.
        have hcj : c j := by
          rcases hjc with h | h
          · exact h
          · exact absurd h hjE
        have hzR_eq : zR N c i = zR N c j := by
          unfold zR
          rw [if_neg hiN, if_neg hjE]
        by_cases hci : c i
        · have hzLi : zL c i = 0 := by
            unfold zL
            rw [if_neg (by rintro ⟨h1, hn⟩; rw [h1] at hci; exact hn hci)]
          by_cases hj1 : j = i + 1
          · rw [if_pos ⟨hj1, hci, hcj⟩] at hnear
            omega
          · have hev : (j - i) % 2 = 0 :=
              Nat.even_iff.mp (hEven i j (by omega) hjN hnone hci hcj)
            rw [if_neg (by rintro ⟨h1, -, -⟩; exact hj1 h1)] at hnear
            omega
        · have hi0 : i = 0 := by
            rcases hT with h | h | h
            · exact h
            · exact absurd h hci
            · omega
          have hc0 : ¬ c 0 := by rw [hi0] at hci; exact hci
          have hzLi : zL c i = 1 := by
            unfold zL
            rw [if_pos ⟨hi0, hc0⟩]
          rw [if_neg (by rintro ⟨-, h1, -⟩; exact hci h1)] at hnear
          have hodd : (j - i) % 2 = 1 := by
            by_cases hj1 : j = i + 1
            · omega
            · have hoj := hOddL j (by omega) hjN
                (fun k hk1 hk2 => hnone k (by omega) hk2) hc0 hcj
              rw [Nat.odd_iff] at hoj
              omega
          omega

theorem yEdge_parity
    (N : ℕ) (hN : 5 ≤ N) (c : ℕ → Prop) [DecidablePred c]
    (hNeven : Even (N - 1))
    (h2 : 2 ≤ ((Finset.range N).filter c).card)
    (hEven : ∀ i j : ℕ, i + 2 ≤ j → j ≤ N - 1 →
        (∀ k, i < k → k < j → ¬ c k) → c i → c j → Even (j - i))
    (hOddL : ∀ j : ℕ, 2 ≤ j → j ≤ N - 1 →
        (∀ k, 0 < k → k < j → ¬ c k) → ¬ c 0 → c j → Odd j)
    (hOddR : ∀ i : ℕ, 0 < i → i + 2 ≤ N - 1 →
        (∀ k, i < k → k < N - 1 → ¬ c k) → c i → ¬ c (N - 1) → Odd (N - 1 - i)) :
    ((Finset.range (N - 1)).filter (fun k => c k ∧ c (k + 1))).card % 2
      = ((if c 0 then 1 else 0) + (if c (N - 1) then 1 else 0)) % 2 := by
  have hk := key N c hN h2 hEven hOddL hOddR (N - 1) 0 (by omega) (by omega) (Or.inl rfl)
  have hy : yFrom N c 0 = ((Finset.range (N - 1)).filter (fun k => c k ∧ c (k + 1))).card := by
    unfold yFrom
    rw [Finset.range_eq_Ico]
  have hzL0 : zL c 0 = if c 0 then 0 else 1 := by
    unfold zL
    by_cases h : c 0
    · rw [if_neg (by rintro ⟨-, hn⟩; exact hn h), if_pos h]
    · rw [if_pos ⟨rfl, h⟩, if_neg h]
  have hzR0 : zR N c 0 = if c (N - 1) then 0 else 1 := by
    unfold zR
    rw [if_neg (by omega : ¬ (0 = N - 1))]
  rw [Nat.even_iff] at hNeven
  rw [hy, hzL0, hzR0] at hk
  split_ifs at hk ⊢ <;> omega

end Workspace.ProofLemmas.Thm183LineCounting
