import Mathlib

open scoped Classical

/-- Abstract fiber pigeonhole (Step 1 of Prop 2.2).

Given nonempty finite types `D` and `C` and any function `Φ : D → C`, there is an
element `η ∈ D` whose fiber `{x | Φ x = Φ η}` has cardinality `|F|` satisfying
`|F| · |C| ≥ |D|`, equivalently `(|F| : ℝ) ≥ |D| / |C|`. -/
theorem IdealClassPigeonholeFiber
    {D C : Type*} [Fintype D] [Fintype C] [Nonempty D] [Nonempty C]
    (Φ : D → C) :
    ∃ η : D,
      Fintype.card {x : D // Φ x = Φ η} * Fintype.card C ≥ Fintype.card D ∧
      (Fintype.card D : ℝ) / (Fintype.card C : ℝ)
        ≤ (Fintype.card {x : D // Φ x = Φ η} : ℝ) := by
  classical
  -- fiber size as a function of the target value
  set g : C → ℕ := fun c => Fintype.card {x : D // Φ x = c} with hg
  -- pick the target with the maximal fiber
  obtain ⟨c₀, hc₀⟩ := Finite.exists_max g
  -- the fibers partition `D`, so their sizes sum to `|D|`
  have hsum : ∑ c : C, g c = Fintype.card D := by
    have hmaps : Set.MapsTo Φ (Finset.univ : Finset D) (Finset.univ : Finset C) := by
      intro x _; exact Finset.mem_univ _
    have hcard := Finset.card_eq_sum_card_fiberwise hmaps
    rw [Finset.card_univ] at hcard
    rw [hcard]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [hg]
    dsimp only
    rw [Fintype.card_subtype]
  -- max fiber times `|C|` dominates the sum, which is `|D|`
  have hle : Fintype.card D ≤ g c₀ * Fintype.card C := by
    rw [← hsum]
    calc ∑ c : C, g c ≤ ∑ _c : C, g c₀ := Finset.sum_le_sum (fun c _ => hc₀ c)
      _ = g c₀ * Fintype.card C := by rw [Finset.sum_const, Finset.card_univ]; ring
  -- max fiber is nonempty
  have hpos : 0 < g c₀ := by
    rcases Nat.eq_zero_or_pos (g c₀) with h | h
    · rw [h, Nat.zero_mul] at hle
      have := Fintype.card_pos (α := D)
      omega
    · exact h
  have hne : Nonempty {x : D // Φ x = c₀} := by
    rw [← Fintype.card_pos_iff]
    exact hpos
  obtain ⟨η, hη⟩ := hne
  -- the fiber over `Φ η` is exactly the max fiber
  have hfib : Fintype.card {x : D // Φ x = Φ η} = g c₀ := by
    simp only [hg, hη]
  refine ⟨η, ?_, ?_⟩
  · rw [hfib, ge_iff_le]
    exact hle
  · have hCpos : (0 : ℝ) < (Fintype.card C : ℝ) := by
      exact_mod_cast Fintype.card_pos (α := C)
    rw [hfib, div_le_iff₀ hCpos]
    exact_mod_cast hle
