import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Workspace.Definitions.ProbDistributions

open BigOperators
open Workspace.Definitions.ProbDistributions
open Classical

namespace Workspace.Lemmas.ProbXpMonotone

/-!
# Monotonicity of `ProbXp` in the parameter `p`

For an upward-closed family `A ⊆ 2^X`, the probability `ProbXp p A` is
non-decreasing in `p ∈ [0,1]`.

The proof proceeds by induction on a finset `U : Finset X` that plays the role
of the "ground set". We define an auxiliary quantity

  `probAux U p A = ∑ S ∈ U.powerset, [S ∈ A] · p^|S| · (1-p)^(|U|-|S|)`

and show:

1. `probAux U` is non-decreasing in `p` on `[0,1]` whenever `A` is upward-closed
   within subsets of `U`.
2. `probAux Finset.univ p A` agrees with `ProbXp p A` (when `U = Finset.univ`,
   `U.powerset` enumerates all subsets and `|U| = Fintype.card X`).

The induction step uses the recurrence

  `probAux (insert x U) p A = (1-p)·α(p) + p·β(p)`

where `α(p) = probAux U p A_no_x` (subsets of `U` already in `A`) and
`β(p) = probAux U p A_with_x` (subsets `S ⊆ U` with `S ∪ {x} ∈ A`), together
with the algebraic identity

  `((1-p₂)α(p₂) + p₂·β(p₂)) - ((1-p₁)α(p₁) + p₁·β(p₁))`
  ` = (1-p₂)·(α(p₂) - α(p₁)) + p₂·(β(p₂) - β(p₁)) + (p₂-p₁)·(β(p₁) - α(p₁))`

Each term is non-negative when `0 ≤ p₁ ≤ p₂ ≤ 1`, by the inductive hypothesis
(applied to `α` and `β`) and the set inclusion `A_no_x ⊆ A_with_x` together
with set monotonicity (`Lemma_ProbXpSetMonotone`).
-/

/-- The standard "Bernoulli weight" of a subset `S` of `U` at parameter `p`. -/
noncomputable def bWeight (p : ℝ) (n k : ℕ) : ℝ :=
  p ^ k * (1 - p) ^ (n - k)

/-- Auxiliary probability over an explicit ground set `U : Finset X`. -/
noncomputable def probAux {X : Type} [DecidableEq X]
    (U : Finset X) (p : ℝ) (A : Set (Finset X)) : ℝ :=
  ∑ S ∈ U.powerset, if S ∈ A then p ^ S.card * (1 - p) ^ (U.card - S.card) else 0

/-- When `U = Finset.univ`, `probAux` reduces to `ProbXp`. -/
lemma probAux_univ_eq_probXp {X : Type} [Fintype X] [DecidableEq X]
    (p : ℝ) (A : Set (Finset X)) :
    probAux (Finset.univ : Finset X) p A = ProbXp p A := by
  unfold probAux ProbXp
  -- `Finset.univ.powerset` enumerates all subsets, in bijection with `Finset X`.
  rw [show (Finset.univ : Finset X).powerset = (Finset.univ : Finset (Finset X)) from
    Finset.eq_univ_iff_forall.mpr (fun S => Finset.mem_powerset.mpr (Finset.subset_univ S))]
  simp [Finset.card_univ]

/-- Set-monotonicity for `probAux`: if `A ⊆ B` then `probAux U p A ≤ probAux U p B`,
    provided `0 ≤ p ≤ 1`. -/
lemma probAux_set_mono {X : Type} [DecidableEq X]
    (U : Finset X) {p : ℝ} (hp_nonneg : 0 ≤ p) (hp_le : p ≤ 1)
    {A B : Set (Finset X)} (hAB : A ⊆ B) :
    probAux U p A ≤ probAux U p B := by
  unfold probAux
  apply Finset.sum_le_sum
  intro S _
  by_cases hSA : S ∈ A
  · have hSB : S ∈ B := hAB hSA
    simp [hSA, hSB]
  · by_cases hSB : S ∈ B
    · simp [hSA, hSB]
      have h1 : 0 ≤ p ^ S.card := pow_nonneg hp_nonneg _
      have h2 : 0 ≤ (1 - p) ^ (U.card - S.card) :=
        pow_nonneg (by linarith) _
      exact mul_nonneg h1 h2
    · simp [hSA, hSB]

/-- Non-negativity of `probAux` for `0 ≤ p ≤ 1`. -/
lemma probAux_nonneg {X : Type} [DecidableEq X]
    (U : Finset X) {p : ℝ} (hp_nonneg : 0 ≤ p) (hp_le : p ≤ 1)
    (A : Set (Finset X)) :
    0 ≤ probAux U p A := by
  unfold probAux
  apply Finset.sum_nonneg
  intro S _
  by_cases hSA : S ∈ A
  · simp [hSA]
    have h1 : 0 ≤ p ^ S.card := pow_nonneg hp_nonneg _
    have h2 : 0 ≤ (1 - p) ^ (U.card - S.card) := pow_nonneg (by linarith) _
    exact mul_nonneg h1 h2
  · simp [hSA]

/-- Recurrence for `probAux` when inserting an element `x` into the ground set `U`.

    Splits subsets `S ⊆ insert x U` into those not containing `x`
    (in bijection with subsets of `U`, via `S ↦ S`) and those containing `x`
    (in bijection with subsets of `U`, via `S ↦ S ∪ {x}`). -/
lemma probAux_insert {X : Type} [DecidableEq X]
    {x : X} {U : Finset X} (hxU : x ∉ U) (p : ℝ) (A : Set (Finset X)) :
    probAux (insert x U) p A
      = (1 - p) * probAux U p A
      + p * probAux U p {S | insert x S ∈ A} := by
  unfold probAux
  -- Split (insert x U).powerset into two disjoint pieces: subsets of U,
  -- and {insert x S | S ⊆ U}.
  have hcard : (insert x U).card = U.card + 1 := Finset.card_insert_of_notMem hxU
  rw [Finset.powerset_insert]
  -- Disjointness: subsets of U don't contain x (so they're not in the image).
  have hdisj : Disjoint (U.powerset) (U.powerset.image (insert x)) := by
    rw [Finset.disjoint_left]
    intro S hS hSimg
    rw [Finset.mem_powerset] at hS
    rw [Finset.mem_image] at hSimg
    obtain ⟨T, _, hTS⟩ := hSimg
    have hxinS : x ∈ S := by
      rw [← hTS]; exact Finset.mem_insert_self x T
    exact hxU (hS hxinS)
  rw [Finset.sum_union hdisj]
  -- Image sum: `∑ S' ∈ U.powerset.image (insert x), f S' = ∑ S ∈ U.powerset, f (insert x S)`.
  have hinjOn : ∀ S1 ∈ U.powerset, ∀ S2 ∈ U.powerset,
      insert x S1 = insert x S2 → S1 = S2 := by
    intro S1 hS1 S2 hS2 heq
    rw [Finset.mem_powerset] at hS1 hS2
    have hx1 : x ∉ S1 := fun h => hxU (hS1 h)
    have hx2 : x ∉ S2 := fun h => hxU (hS2 h)
    have h1 : (insert x S1).erase x = S1 := Finset.erase_insert hx1
    have h2 : (insert x S2).erase x = S2 := Finset.erase_insert hx2
    rw [← h1, ← h2, heq]
  rw [Finset.sum_image hinjOn]
  -- After `sum_union` and `sum_image`, both LHS pieces are sums over
  -- `U.powerset`. Multiply through on the RHS and align term-by-term.
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro S hS
    rw [Finset.mem_powerset] at hS
    have hxS : x ∉ S := fun h => hxU (hS h)
    have hSU : S.card ≤ U.card := Finset.card_le_card hS
    have hsuc1 : (insert x U).card - S.card = (U.card - S.card) + 1 := by
      rw [hcard]; omega
    by_cases h1 : S ∈ A
    · simp only [h1, if_true]
      rw [hsuc1]
      ring
    · simp [h1]
  · apply Finset.sum_congr rfl
    intro S hS
    rw [Finset.mem_powerset] at hS
    have hxS : x ∉ S := fun h => hxU (hS h)
    have hSU : S.card ≤ U.card := Finset.card_le_card hS
    have hSic : (insert x S).card = S.card + 1 := Finset.card_insert_of_notMem hxS
    have hsuc2 : (insert x U).card - (insert x S).card = U.card - S.card := by
      rw [hcard, hSic]; omega
    by_cases h2 : insert x S ∈ A
    · have h2' : S ∈ {S : Finset X | insert x S ∈ A} := h2
      simp only [h2, h2', if_true]
      rw [hsuc2, hSic]
      ring
    · have h2' : S ∉ {S : Finset X | insert x S ∈ A} := h2
      simp [h2, h2']

/-- Auxiliary lemma: under upward-closure, the family `A` (no x) is contained
    in `{S | insert x S ∈ A}` (with x). -/
lemma upward_closed_no_x_subset_with_x {X : Type} [DecidableEq X]
    {x : X} {A : Set (Finset X)}
    (hA : ∀ {S1 S2 : Finset X}, S1 ∈ A → S1 ⊆ S2 → S2 ∈ A) :
    {S : Finset X | S ∈ A} ⊆ {S : Finset X | insert x S ∈ A} := by
  intro S hS
  exact hA hS (Finset.subset_insert _ _)

/-- Upward-closure descends to the subfamilies used in the recurrence. -/
lemma upward_closed_descends {X : Type} [DecidableEq X]
    {A : Set (Finset X)}
    (hA : ∀ {S1 S2 : Finset X}, S1 ∈ A → S1 ⊆ S2 → S2 ∈ A) (x : X) :
    (∀ {S1 S2 : Finset X}, S1 ∈ A → S1 ⊆ S2 → S2 ∈ A)
    ∧ (∀ {S1 S2 : Finset X}, insert x S1 ∈ A → S1 ⊆ S2 → insert x S2 ∈ A) := by
  refine ⟨hA, ?_⟩
  intro S1 S2 hS1 hsub
  exact hA hS1 (Finset.insert_subset_insert x hsub)

/-- Algebraic identity used in the induction step. -/
lemma alg_identity (p1 p2 α1 α2 β1 β2 : ℝ) :
    ((1 - p2) * α2 + p2 * β2) - ((1 - p1) * α1 + p1 * β1)
      = (1 - p2) * (α2 - α1) + p2 * (β2 - β1) + (p2 - p1) * (β1 - α1) := by
  ring

/-- The core inductive lemma, on the ground set `U`.

    To make the induction hypothesis applicable to the auxiliary family
    `{S | insert x S ∈ A}` that arises in the recurrence, we generalize `A`
    (i.e., the IH must quantify over arbitrary upward-closed families `A`). -/
lemma probAux_mono_on_finset {X : Type} [DecidableEq X]
    (U : Finset X) {p1 p2 : ℝ}
    (hp1_nonneg : 0 ≤ p1) (hp : p1 ≤ p2) (hp2_le : p2 ≤ 1) :
    ∀ (A : Set (Finset X)),
    (∀ {S1 S2 : Finset X}, S1 ∈ A → S1 ⊆ S2 → S2 ∈ A) →
    probAux U p1 A ≤ probAux U p2 A := by
  induction U using Finset.induction_on with
  | empty =>
    intro A _
    -- Base case: `U = ∅`, `U.powerset = {∅}`. Both sides equal
    -- `[∅ ∈ A] · 1 · 1`, and the inequality is reflexive.
    unfold probAux
    by_cases h0 : (∅ : Finset X) ∈ A
    · simp [h0]
    · simp [h0]
  | @insert x U hxU ih =>
    intro A hA
    -- Step case: use the recurrence and the algebraic identity.
    have hp1_le_one : p1 ≤ 1 := le_trans hp hp2_le
    have hp2_nonneg : 0 ≤ p2 := le_trans hp1_nonneg hp
    have h1mp1 : 0 ≤ 1 - p1 := by linarith
    have h1mp2 : 0 ≤ 1 - p2 := by linarith
    -- Decompose both sides via the recurrence.
    have hrec1 := probAux_insert (x := x) (U := U) hxU p1 A
    have hrec2 := probAux_insert (x := x) (U := U) hxU p2 A
    -- Define α and β for both p1 and p2.
    set α1 := probAux U p1 A
    set α2 := probAux U p2 A
    set Awith : Set (Finset X) := {S | insert x S ∈ A}
    set β1 := probAux U p1 Awith
    set β2 := probAux U p2 Awith
    -- IH applied to A (using α monotonicity).
    have hα : α1 ≤ α2 := ih A @hA
    -- Awith is upward closed, so IH applies (β monotonicity).
    have hAwith : ∀ {S1 S2 : Finset X}, S1 ∈ Awith → S1 ⊆ S2 → S2 ∈ Awith := by
      intro S1 S2 hS1 hsub
      exact hA hS1 (Finset.insert_subset_insert x hsub)
    have hβ : β1 ≤ β2 := ih Awith @hAwith
    -- A ⊆ Awith (set inclusion), hence at parameter p1 we have α1 ≤ β1
    -- (set monotonicity).
    have hAsub : A ⊆ Awith := by
      intro S hS
      exact hA hS (Finset.subset_insert x S)
    have hαβ : α1 ≤ β1 :=
      probAux_set_mono U hp1_nonneg hp1_le_one hAsub
    -- Now use the algebraic identity.
    rw [hrec1, hrec2]
    have hid := alg_identity p1 p2 α1 α2 β1 β2
    have ht1 : 0 ≤ (1 - p2) * (α2 - α1) :=
      mul_nonneg h1mp2 (sub_nonneg.mpr hα)
    have ht2 : 0 ≤ p2 * (β2 - β1) :=
      mul_nonneg hp2_nonneg (sub_nonneg.mpr hβ)
    have ht3 : 0 ≤ (p2 - p1) * (β1 - α1) :=
      mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hαβ)
    linarith

/-- **Main theorem**: monotonicity of `ProbXp` in `p` on `[0,1]` for upward-closed
    families. -/
theorem prob_xp_monotone {X : Type} [Fintype X] {p1 p2 : ℝ}
    (hp1_nonneg : 0 ≤ p1) (hp : p1 ≤ p2) (hp2_le : p2 ≤ 1)
    (A : Set (Finset X))
    (hA : ∀ {S1 S2 : Finset X}, S1 ∈ A → S1 ⊆ S2 → S2 ∈ A) :
    ProbXp p1 A ≤ ProbXp p2 A := by
  classical
  -- Reduce to the auxiliary finset version with `U = Finset.univ`.
  rw [← probAux_univ_eq_probXp p1 A, ← probAux_univ_eq_probXp p2 A]
  exact probAux_mono_on_finset (Finset.univ : Finset X) hp1_nonneg hp hp2_le A @hA

end Workspace.Lemmas.ProbXpMonotone
