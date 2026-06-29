import Mathlib
import Workspace.Types.BinVec
import Workspace.Types.AlternatingSumExpression

open scoped BigOperators

theorem AltSumExpansionMatches :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
    ∀ (δ α : ℝ),
      ∑ m : Workspace.Types.BinVec.BinVec (n / 2),
        (if (∀ j₁ j₂ : Fin (n / 2),
                m.bit j₁ = true → m.bit j₂ = true → j₁.val % 2 = j₂.val % 2)
         then ∑ zMinus ∈ Finset.range (n / 2 + 1),
                ∑ zPlus ∈ Finset.range (n / 2 + 1),
                  |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus
                    (((Finset.univ : Finset (Fin (n / 2))).filter
                        (fun j => m.bit j = true)).image
                      (fun j => j.val + 1))|
         else (0 : ℝ))
      = Workspace.Types.AlternatingSumExpression.altSum n δ α := by
  intro n hn hmod δ α
  -- Helper function: the inner z₋, z₊ sum in absolute value
  set S : Finset ℕ → ℝ := fun ℓ =>
    ∑ zMinus ∈ Finset.range (n / 2 + 1),
      ∑ zPlus ∈ Finset.range (n / 2 + 1),
        |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ| with hS
  -- The map BinVec (n/2) → Finset ℕ
  set φ : Workspace.Types.BinVec.BinVec (n / 2) → Finset ℕ := fun m =>
    ((Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)).image
      (fun j => j.val + 1) with hφ
  -- Predicate on m
  set P : Workspace.Types.BinVec.BinVec (n / 2) → Prop := fun m =>
    ∀ j₁ j₂ : Fin (n / 2),
      m.bit j₁ = true → m.bit j₂ = true → j₁.val % 2 = j₂.val % 2 with hP
  -- Step 1: Rewrite the RHS using Finset.sum_powerset (reverse stratification)
  have h_card : (Finset.Icc 1 (n / 2)).card = n / 2 := by
    rw [Nat.card_Icc]; omega
  -- altSum unfolds to: ∑ ℓ ∈ (Icc 1 (n/2)).powerset.filter sameParity, S ℓ
  have hAltSum :
      Workspace.Types.AlternatingSumExpression.altSum n δ α
        = ∑ ℓ ∈ ((Finset.Icc 1 (n / 2)).powerset).filter
            Workspace.Types.AlternatingSumExpression.sameParity, S ℓ := by
    unfold Workspace.Types.AlternatingSumExpression.altSum
    unfold Workspace.Types.AlternatingSumExpression.innerSumOverEll
    -- Switch each inner ∑ ℓ ∈ filter sameParity, ... to ∑ ℓ ∈ powersetCard k, if sameParity then S ℓ else 0
    have hk : ∀ k,
        ∑ ℓ ∈ ((Finset.Icc 1 (n / 2)).powersetCard k).filter
                Workspace.Types.AlternatingSumExpression.sameParity,
            ∑ zMinus ∈ Finset.range (n / 2 + 1),
              ∑ zPlus ∈ Finset.range (n / 2 + 1),
                |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|
        = ∑ ℓ ∈ (Finset.Icc 1 (n / 2)).powersetCard k,
            (if Workspace.Types.AlternatingSumExpression.sameParity ℓ then S ℓ else 0) := by
      intro k
      rw [Finset.sum_filter]
    simp_rw [hk]
    -- Use Finset.sum_powerset reversed
    rw [show n / 2 + 1 = (Finset.Icc 1 (n / 2)).card + 1 from by rw [h_card],
        ← Finset.sum_powerset]
    -- Now switch to filter via Finset.sum_filter
    rw [Finset.sum_filter]
  rw [hAltSum]
  -- Step 2: Rewrite LHS via Finset.sum_filter (treating sum over Fintype as sum over univ)
  -- The LHS is ∑ m, if P m then S (φ m) else 0 = ∑ m ∈ univ.filter P, S (φ m)
  have hLHS_eq :
      (∑ m : Workspace.Types.BinVec.BinVec (n / 2),
         (if (∀ j₁ j₂ : Fin (n / 2),
                m.bit j₁ = true → m.bit j₂ = true → j₁.val % 2 = j₂.val % 2)
          then ∑ zMinus ∈ Finset.range (n / 2 + 1),
                  ∑ zPlus ∈ Finset.range (n / 2 + 1),
                  |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus
                    (((Finset.univ : Finset (Fin (n / 2))).filter
                        (fun j => m.bit j = true)).image
                      (fun j => j.val + 1))|
          else (0 : ℝ)))
        = ∑ m ∈ (Finset.univ : Finset (Workspace.Types.BinVec.BinVec (n / 2))).filter P,
            S (φ m) := by
    rw [← Finset.sum_filter]
  rw [hLHS_eq]
  -- Step 3: Bijection via Finset.sum_bij
  apply Finset.sum_bij (fun m _ => φ m)
  · -- membership
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨_, hPm⟩ := hm
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · -- φ m ∈ powerset of Icc 1 (n/2)
      rw [Finset.mem_powerset]
      intro x hx
      simp only [hφ, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨j, _, hj⟩ := hx
      rw [Finset.mem_Icc]
      refine ⟨?_, ?_⟩
      · omega
      · have := j.isLt
        omega
    · -- sameParity (φ m)
      intro a ha b hb
      simp only [hφ, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      obtain ⟨j₁, hj₁, hja⟩ := ha
      obtain ⟨j₂, hj₂, hjb⟩ := hb
      have hpar := hPm j₁ j₂ hj₁ hj₂
      omega
  · -- injectivity
    intro m₁ hm₁ m₂ hm₂ heq
    -- φ m₁ = φ m₂ implies m₁ = m₂
    cases m₁ with
    | mk b₁ =>
    cases m₂ with
    | mk b₂ =>
    congr 1
    funext j
    simp only [hφ] at heq
    -- For any j, j.val + 1 ∈ φ m ↔ m.bit j = true
    have hmem : ∀ (b : Fin (n / 2) → Bool) (j : Fin (n / 2)),
        (j.val + 1) ∈ ((Finset.univ : Finset (Fin (n / 2))).filter
            (fun k => b k = true)).image (fun k => k.val + 1)
          ↔ b j = true := by
      intro b j
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨k, hk, hk'⟩
        have heqj : k = j := Fin.ext (by omega)
        rw [heqj] at hk
        exact hk
      · intro h
        exact ⟨j, h, rfl⟩
    have h1 := hmem b₁ j
    have h2 := hmem b₂ j
    rw [heq] at h1
    by_cases hb : b₁ j = true
    · have := h1.mpr hb
      have hb2 := h2.mp this
      rw [hb, hb2]
    · have hb' : b₁ j = false := by
        cases h : b₁ j with
        | true => exact absurd h hb
        | false => rfl
      -- b₂ j = false too
      have hcontra : ¬ ((j.val + 1) ∈ ((Finset.univ : Finset (Fin (n / 2))).filter
              (fun k => b₂ k = true)).image (fun k => k.val + 1)) := by
        intro hin
        have := h1.mp (heq ▸ hin)
        rw [hb'] at this
        exact Bool.false_ne_true this
      have hnot2 : ¬ (b₂ j = true) := fun h => hcontra (h2.mpr h)
      cases h : b₂ j with
      | true => exact absurd h hnot2
      | false => rw [hb']
  · -- surjectivity
    intro ℓ hℓ
    rw [Finset.mem_filter, Finset.mem_powerset] at hℓ
    obtain ⟨hℓ_sub, hℓ_par⟩ := hℓ
    -- Build m : BinVec (n/2) from ℓ
    refine ⟨⟨fun j => decide ((j.val + 1) ∈ ℓ)⟩, ?_, ?_⟩
    · -- membership in filter
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro j₁ j₂ hj₁ hj₂
      simp only [decide_eq_true_eq] at hj₁ hj₂
      have hpar := hℓ_par _ hj₁ _ hj₂
      omega
    · -- φ m = ℓ
      simp only [hφ]
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
                 decide_eq_true_eq]
      constructor
      · rintro ⟨j, hj, hxj⟩
        rw [← hxj]; exact hj
      · intro hx
        have hxIcc : x ∈ Finset.Icc 1 (n / 2) := hℓ_sub hx
        rw [Finset.mem_Icc] at hxIcc
        obtain ⟨hx1, hxN⟩ := hxIcc
        refine ⟨⟨x - 1, by omega⟩, ?_, ?_⟩
        · simp only
          have hsub : x - 1 + 1 = x := by omega
          rw [hsub]; exact hx
        · simp; omega
  · -- pointwise equality of summands
    intro m hm
    rfl
