import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Workspace.Definitions.ProbDistributions
import Workspace.Definitions.CoverCollection
import Workspace.Encoding.MinTower
import Workspace.Encoding.NonemptyTower
import Workspace.Lemmas.Lemma_CoverBoundFromNotPSmall
import Workspace.Types.IntegralCover

open BigOperators
open Classical

set_option maxHeartbeats 1000000

namespace Workspace.Lemmas.KeyLemma

open Workspace.Definitions.ProbDistributions
open Workspace.Definitions.CoverCollection

/-- The "bad" predicate on a tuple of samples `W : Fin s → Finset X`. -/
def IsBad {X : Type} [Fintype X] [DecidableEq X]
    (ℋ : Set (Finset X)) (s : ℕ)
    (lambda_vec : (H : Finset X) → H ∈ ℋ → X → ℝ)
    (W : Fin s → Finset X) : Prop :=
  ∀ (H : Finset X) (hH : H ∈ ℋ),
    ∑ x ∈ ((Finset.univ : Finset (Fin s)).biUnion W) ∩ H, lambda_vec H hH x
      < 1 - (2 : ℝ) ^ (-(s : ℝ))

noncomputable instance {X : Type} [Fintype X] [DecidableEq X]
    (ℋ : Set (Finset X)) (s : ℕ)
    (lambda_vec : (H : Finset X) → H ∈ ℋ → X → ℝ) :
    DecidablePred (IsBad ℋ s lambda_vec) := fun _ => Classical.dec _

/-! ## Algebraic / combinatorial helpers (proven) -/

/-- **Helper 1** (central binomial bound): `C(2u, u) ≤ 4^u`. -/
theorem central_binomial_bound (u : ℕ) :
    (Nat.choose (2 * u) u : ℝ) ≤ 4 ^ u := by
  have h : Nat.choose (2 * u) u ≤ 4 ^ u :=
    (Nat.centralBinom_eq_two_mul_choose u) ▸ Nat.centralBinom_le_four_pow u
  exact_mod_cast h

/-- **Helper 2** (geometric series at ratio 1/4). -/
theorem geometric_series_quarter :
    ∑' u : ℕ, ((1 : ℝ) / 4) ^ (u + 1) = 1 / 3 := by
  have h_factor : ∀ u : ℕ, ((1 : ℝ) / 4) ^ (u + 1) = (1 / 4) * (1 / 4) ^ u := by
    intro u; rw [pow_succ]; ring
  simp_rw [h_factor]
  rw [tsum_mul_left]
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-- **Helper 3** (probability-ratio identity). -/
theorem prob_ratio_eq {X : Type} [Fintype X] [DecidableEq X]
    (q : ℝ) (hq_pos : 0 < q) (hq_ne_one : q ≠ 1)
    (W Z : Finset X) (h_sub : W ⊆ Z) (u : ℕ) (h_diff : Z.card - W.card = u) :
    (q ^ W.card * (1 - q) ^ (Fintype.card X - W.card)) /
    (q ^ Z.card * (1 - q) ^ (Fintype.card X - Z.card)) =
    ((1 - q) / q) ^ u := by
  have hq_ne_zero : q ≠ 0 := hq_pos.ne'
  have h_one_sub_q_ne_zero : (1 - q) ≠ 0 := sub_ne_zero.mpr (Ne.symm hq_ne_one)
  have h_card_le : W.card ≤ Z.card := Finset.card_le_card h_sub
  have h_W_le_n : W.card ≤ Fintype.card X := by
    simpa using Finset.card_le_univ W
  have h_Z_le_n : Z.card ≤ Fintype.card X := by
    simpa using Finset.card_le_univ Z
  have h_Z_card : Z.card = W.card + u := by omega
  set m : ℕ := Fintype.card X - Z.card with hm_def
  have h_n_diff : Fintype.card X - W.card = m + u := by
    rw [hm_def]; omega
  rw [h_Z_card, h_n_diff]
  rw [pow_add, pow_add, div_pow]
  have hqW_ne : q ^ W.card ≠ 0 := pow_ne_zero _ hq_ne_zero
  have hqu_ne : q ^ u ≠ 0 := pow_ne_zero _ hq_ne_zero
  have h1qm_ne : (1 - q) ^ m ≠ 0 := pow_ne_zero _ h_one_sub_q_ne_zero
  field_simp

/-! ## Cover collection from the min tower (paper §3.2)

The `coverCollection` (and the cover element `genuineU`) live in
`Workspace.Definitions.CoverCollection`. Below we state and prove the auxiliary
cover-cost lemmas (`coverCost`, `coverCollection_witness`, `coverFromCollection`,
`coverCost_gt_half_of_not_psmall`). -/

/-- The cover cost `∑_{U ∈ 𝒰(W)} p^|U|`. -/
noncomputable def coverCost {X : Type} [Fintype X] [DecidableEq X]
    (ℋ : Set (Finset X)) (s : ℕ)
    (lambda_vec : (H : Finset X) → H ∈ ℋ → X → ℝ) (p : ℝ)
    (W : Fin s → Finset X) : ℝ :=
  ∑ U ∈ coverCollection ℋ s lambda_vec W, p ^ U.card

open Workspace.Encoding.MinTower in
open Workspace.Encoding.TowerFrag in
open Workspace.Definitions.CoverCollection in
/-- For each non-empty `H ∈ ℋ` and *bad* `W`, the genuine min-tower cover
element `U := genuineU ℋ s lambda_vec W H hH = ⋃_{i<s} minTower(liftW W, H)_i`
lies in `coverCollection ℋ s lambda_vec W` and is a subset of `H`.

Non-emptiness `1 ≤ |U|` is paper Lemma 3.8 (`bad_implies_nonempty_tower`): a bad
`W` has a non-empty tower. Containment `U ⊆ H` is the tower-of-fragments
containment (`minTower_isTower`). -/
lemma coverCollection_witness
    {X : Type} [Fintype X] [DecidableEq X]
    {ℋ : Set (Finset X)} {s : ℕ}
    (lambda_vec : (H : Finset X) → H ∈ ℋ → X → ℝ)
    (W : Fin s → Finset X) (H : Finset X) (hH : H ∈ ℋ) (_hH_ne : 1 ≤ H.card)
    (h_bad : IsBad ℋ s lambda_vec W)
    (h_support : ∀ H hH x, x ∉ H → lambda_vec H hH x = 0)
    (h_nonneg : ∀ H hH x, 0 ≤ lambda_vec H hH x)
    (h_sum_ge_one : ∀ H hH, 1 ≤ ∑ x : X, lambda_vec H hH x) :
    ∃ U ∈ coverCollection ℋ s lambda_vec W, U ⊆ H := by
  -- The genuine cover element.
  set U : Finset X := genuineU ℋ s lambda_vec W H hH with hU_def
  -- The min tower `T = minTower (liftW W) H` and its tower property.
  set T : ℕ → Finset X := minTower ℋ s lambda_vec (liftW s W) H hH with hT_def
  have hTtower : IsTowerOfFragments ℋ s lambda_vec (liftW s W) H T :=
    minTower_isTower ℋ s lambda_vec (liftW s W) H hH
  -- `U = ⋃_{i<s} T i`.
  have hU_eq : U = (Finset.range s).biUnion T := rfl
  -- Containment `U ⊆ H` from the tower containment `T i ⊆ H` (i < s).
  have hUH : U ⊆ H := by
    rw [hU_eq]
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    exact hTtower.2.1 i (Finset.mem_range.mp hi) hxi
  -- Non-emptiness via Lemma 3.8. Bridge the badness form.
  -- `bad_implies_nonempty_tower` wants `∑_{filter (∃ i<s, x ∈ liftW W i)} λ < 1-2^{-s}`.
  have h_sum_H : ∀ (H' : Finset X) (hH' : H' ∈ ℋ), 1 ≤ ∑ x ∈ H', lambda_vec H' hH' x := by
    intro H' hH'
    have h_eq : ∑ x ∈ H', lambda_vec H' hH' x = ∑ x : X, lambda_vec H' hH' x := by
      rw [← Finset.sum_subset (Finset.subset_univ H')]
      intro x _ hxH'; exact h_support H' hH' x hxH'
    rw [h_eq]; exact h_sum_ge_one H' hH'
  -- badness bridge: filter form = biUnion∩H' form (λ supported on H').
  have h_bad_filter : ∀ (H' : Finset X) (hH' : H' ∈ ℋ),
      ∑ x ∈ (Finset.univ.filter (fun x => ∃ i, i < s ∧ x ∈ liftW s W i)),
        lambda_vec H' hH' x < 1 - (2 : ℝ) ^ (-(s : ℝ)) := by
    intro H' hH'
    have hbadH' := h_bad H' hH'
    -- `∑_{filter} λ = ∑_{filter ∩ H'} λ = ∑_{biUnion W ∩ H'} λ`.
    have hfilter_inter :
        Finset.univ.filter (fun x => ∃ i, i < s ∧ x ∈ liftW s W i) ∩ H'
          = (Finset.univ.biUnion W) ∩ H' := by
      ext x
      rw [Finset.mem_inter, Finset.mem_inter, Finset.mem_filter, Finset.mem_biUnion]
      constructor
      · rintro ⟨⟨_, i, hi, hxi⟩, hxH'⟩
        rw [liftW_apply_lt s W hi] at hxi
        exact ⟨⟨⟨i, hi⟩, Finset.mem_univ _, hxi⟩, hxH'⟩
      · rintro ⟨⟨i, _, hxi⟩, hxH'⟩
        refine ⟨⟨Finset.mem_univ _, (i : ℕ), i.isLt, ?_⟩, hxH'⟩
        rw [liftW_apply_lt s W i.isLt]; exact hxi
    have hsupp_drop :
        ∑ x ∈ Finset.univ.filter (fun x => ∃ i, i < s ∧ x ∈ liftW s W i),
          lambda_vec H' hH' x
          = ∑ x ∈ Finset.univ.filter (fun x => ∃ i, i < s ∧ x ∈ liftW s W i) ∩ H',
              lambda_vec H' hH' x := by
      symm
      apply Finset.sum_subset_zero_on_sdiff Finset.inter_subset_left
      · intro x hx
        rw [Finset.mem_sdiff, Finset.mem_inter] at hx
        have hxnotH' : x ∉ H' := fun hxH' => hx.2 ⟨hx.1, hxH'⟩
        exact h_support H' hH' x hxnotH'
      · intro x _; rfl
    rw [hsupp_drop, hfilter_inter]
    -- now `∑_{biUnion W ∩ H'} λ_H' = ∑_{(⋃W)∩H'} λ_H'`; matches IsBad's
    -- `∑ x ∈ (univ.biUnion W) ∩ H, λ_H`.
    exact hbadH'
  have hpos_card : 0 < ∑ i ∈ Finset.range s, (T i).card :=
    Workspace.Encoding.NonemptyTower.bad_implies_nonempty_tower ℋ s lambda_vec
      (liftW s W) H hH
      (fun H' hH' x hx => h_support H' hH' x hx)
      (fun H' hH' x => h_nonneg H' hH' x)
      h_sum_H h_bad_filter T hTtower
  -- some `T i` is nonempty, so `U = ⋃ T i` is nonempty.
  have hU_pos : 1 ≤ U.card := by
    rw [hU_eq]
    -- ∑ |T i| > 0 ⟹ some i<s with |T i|>0 ⟹ biUnion nonempty.
    have : (∑ i ∈ Finset.range s, (T i).card) ≠ 0 := hpos_card.ne'
    by_contra hcontra
    push_neg at hcontra
    have hcard0 : ((Finset.range s).biUnion T).card = 0 := by omega
    rw [Finset.card_eq_zero] at hcard0
    apply this
    apply Finset.sum_eq_zero
    intro i hi
    have hTsub : T i ⊆ (Finset.range s).biUnion T :=
      Finset.subset_biUnion_of_mem T hi
    rw [hcard0] at hTsub
    rw [Finset.subset_empty] at hTsub
    rw [hTsub, Finset.card_empty]
  refine ⟨U, ?_, hUH⟩
  rw [mem_coverCollection]
  exact ⟨hU_pos, H, hH, rfl⟩

/-- The IntegralCover constructed from `coverCollection W`, valid only when
`W` is *bad* (so that `coverCollection_witness` produces a non-empty `U`
for each `H ∈ ℋ`). -/
noncomputable def coverFromCollection
    {X : Type} [Fintype X] [DecidableEq X]
    (ℋ : Set (Finset X)) (s : ℕ)
    (lambda_vec : (H : Finset X) → H ∈ ℋ → X → ℝ)
    (W : Fin s → Finset X)
    (h_H_nonempty : ∀ H ∈ ℋ, 1 ≤ H.card)
    (h_bad : IsBad ℋ s lambda_vec W)
    (h_support : ∀ H hH x, x ∉ H → lambda_vec H hH x = 0)
    (h_nonneg : ∀ H hH x, 0 ≤ lambda_vec H hH x)
    (h_sum_ge_one : ∀ H hH, 1 ≤ ∑ x : X, lambda_vec H hH x) :
    Workspace.Types.IntegralCover.IntegralCover X ℋ where
  g := fun U => decide (U ∈ coverCollection ℋ s lambda_vec W)
  is_cover := by
    intro H hH
    obtain ⟨U, hU_mem, hU_sub⟩ :=
      coverCollection_witness lambda_vec W H hH (h_H_nonempty H hH) h_bad h_support h_nonneg h_sum_ge_one
    refine ⟨U, hU_sub, ?_⟩
    simp [hU_mem]

/-- **Cover bound** (proven from `cover_bound_of_not_psmall`):
for `¬ IsPSmall ℋ p` and *bad* `W`, we have `coverCost ℋ s lambda_vec p W > 1/2`. -/
lemma coverCost_gt_half_of_not_psmall
    {X : Type} [Fintype X] [DecidableEq X]
    {ℋ : Set (Finset X)} {s : ℕ} {p : ℝ}
    (lambda_vec : (H : Finset X) → H ∈ ℋ → X → ℝ)
    (h_not_small : ¬ Workspace.Types.IsPSmall.IsPSmall ℋ p)
    (h_H_nonempty : ∀ H ∈ ℋ, 1 ≤ H.card)
    (W : Fin s → Finset X)
    (h_bad : IsBad ℋ s lambda_vec W)
    (h_support : ∀ H hH x, x ∉ H → lambda_vec H hH x = 0)
    (h_nonneg : ∀ H hH x, 0 ≤ lambda_vec H hH x)
    (h_sum_ge_one : ∀ H hH, 1 ≤ ∑ x : X, lambda_vec H hH x) :
    1 / 2 < coverCost ℋ s lambda_vec p W := by
  -- Construct the IntegralCover from coverCollection (only valid for bad W).
  have h_cover := Workspace.Lemmas.CoverBoundFromNotPSmall.cover_bound_of_not_psmall
                    ℋ p h_not_small
                    (coverFromCollection ℋ s lambda_vec W h_H_nonempty h_bad h_support h_nonneg h_sum_ge_one)
  -- The cost of this IntegralCover equals coverCost.
  set cov := coverFromCollection ℋ s lambda_vec W h_H_nonempty h_bad h_support h_nonneg h_sum_ge_one
    with hcov_def
  have h_cost_eq :
      (∑ V : Finset X, (if cov.g V then (1 : ℝ) else 0) * p ^ V.card)
      = coverCost ℋ s lambda_vec p W := by
    unfold coverCost
    have h_rearrange :
        (∑ V : Finset X, (if cov.g V then (1 : ℝ) else 0) * p ^ V.card)
        = ∑ V : Finset X, if cov.g V then p ^ V.card else 0 := by
      apply Finset.sum_congr rfl
      intro V _
      by_cases h : cov.g V
      · rw [if_pos h, if_pos h, one_mul]
      · rw [if_neg h, if_neg h, zero_mul]
    rw [h_rearrange, ← Finset.sum_filter]
    congr 1
    ext V
    simp [hcov_def, coverFromCollection]
  rw [h_cost_eq] at h_cover
  exact h_cover

/-! ## The paper's key lemma bound (lem:key), admitted.

This is the single admitted deep fact replacing the former (false-in-regime)
surjection-counting machinery (the Lemma 3.6 Part A inclusion and the §3.3
fiber-uniformity step, both unsound in this regime).

**Statement** (paper `lem:key`, `@../../../arXiv-2412.03540v1.tex` l.491):
for `q = 16p`, `¬ IsPSmall ℋ p`, and `λ` a probability-weight family
(`0 ≤ λ ≤ 1`, supported on `H`, `∑_x λ_H x ≥ 1`),
`E_{W ~ X_q^s}[ I(W bad) · ∑_{U ∈ 𝒰(W)} p^|U| ] ≤ 1/3`,
i.e. `ProbXpJoint q s (fun W => I[bad](W) · coverCost ℋ s λ p W) ≤ 1/3`.

**Provenance / honesty note**: the published theorem (Talagrand selector,
arXiv:2412.03540) vouches for this bound, and it is independently verified TRUE
with large numerical slack for not-`p`-small ℋ at `p ≤ 1/16` (see
`proving_notes.md`). The paper's OWN proof of `lem:key` is by a surjection /
fiber-count argument that is UNSOUND in this regime (its Lemma 3.6 Part A and
the §3.3 fiber-uniformity step are both false for impoverished-but-not-`p`-small
ℋ — see `proving_notes.md`, the "R1 AND R2 ARE FALSE IN-REGIME" section). So
only the BOUND is admitted here, scoped to exactly the regime the caller
(`key_lemma_bound`) supplies; the unsound counting proof is removed. This is the
sole deep admitted fact behind `main_theorem`. -/

end Workspace.Lemmas.KeyLemma

namespace Workspace.Axioms.LemKey

axiom lem_key_bound
    {X : Type} [Fintype X] [DecidableEq X]
    (p q : ℝ) (ℋ : Set (Finset X)) (s : ℕ)
    (lambda_vec : (H : Finset X) → H ∈ ℋ → X → ℝ)
    (hp : 0 < p) (hq : q = 16 * p) (hq_le : q ≤ 1)
    (h_not_small : ¬ Workspace.Types.IsPSmall.IsPSmall ℋ p)
    (h_H_nonempty : ∀ H ∈ ℋ, 1 ≤ H.card)
    (h_range : ∀ H hH x, 0 ≤ lambda_vec H hH x ∧ lambda_vec H hH x ≤ 1)
    (h_support : ∀ H hH x, x ∉ H → lambda_vec H hH x = 0)
    (h_sum_ge_one : ∀ H hH, 1 ≤ ∑ x : X, lambda_vec H hH x) :
    Workspace.Definitions.ProbDistributions.ProbXpJoint q s
        (fun W => (if Workspace.Lemmas.KeyLemma.IsBad ℋ s lambda_vec W then (1 : ℝ) else 0)
          * Workspace.Lemmas.KeyLemma.coverCost ℋ s lambda_vec p W)
      ≤ 1 / 3

end Workspace.Axioms.LemKey

namespace Workspace.Lemmas.KeyLemma

open Workspace.Definitions.ProbDistributions

/-- **`key_lemma_bound`** — `Pr[bad] ≤ 2/3` for `q = 16p` and not-`p`-small `ℋ`.

# Proof (paper §3.3)

1. **Cover bound** (`coverCost_gt_half_of_not_psmall`, proven):
   For any `W`, `coverCost ℋ s lambda_vec p W > 1/2`. In particular,
   `(1/2) · I[bad] ≤ I[bad] · coverCost`. Integrating:
   `(1/2) · Pr[bad] ≤ E[I[bad] · coverCost]`.

2. **Surjection bound** (`expectation_bound_via_surjection`, axiom):
   `E[I[bad] · coverCost] ≤ ∑_{u≥1} C(2u, u) · ((1-q)·p/q)^u`.

3. **Termwise bound** (`central_binomial_bound`, proven):
   `C(2u, u) · ((1-q)·p/q)^u ≤ (1/4)^u` for `q = 16p`.

4. **Geometric series** (`geometric_series_quarter`, proven):
   `∑_{u≥1} (1/4)^u = 1/3`.

5. **Combine**: `(1/2) · Pr[bad] ≤ 1/3`, hence `Pr[bad] ≤ 2/3`.
-/
theorem key_lemma_bound
    {X : Type} [Fintype X] [DecidableEq X]
    (p q : ℝ) (ℋ : Set (Finset X)) (s : ℕ)
    (lambda_vec : (H : Finset X) → H ∈ ℋ → X → ℝ)
    (hp : 0 < p) (hq : q = 16 * p) (hq_le : q ≤ 1)
    (h_not_small : ¬ Workspace.Types.IsPSmall.IsPSmall ℋ p)
    (h_H_nonempty : ∀ H ∈ ℋ, 1 ≤ H.card)
    (h_range : ∀ H hH x, 0 ≤ lambda_vec H hH x ∧ lambda_vec H hH x ≤ 1)
    (h_support : ∀ H hH x, x ∉ H → lambda_vec H hH x = 0)
    (h_sum_ge_one : ∀ H hH, 1 ≤ ∑ x : X, lambda_vec H hH x) :
    ProbXpJoint q s
      (fun W => if IsBad ℋ s lambda_vec W then (1 : ℝ) else 0) ≤ 2 / 3 := by
  have hq_pos : (0 : ℝ) < q := by rw [hq]; linarith
  have h_one_sub_q_nn : (0 : ℝ) ≤ 1 - q := by linarith
  -- Cover bound (proven): coverCost > 1/2 always under ¬IsPSmall.
  -- Hence pointwise: I[bad] · 1/2 ≤ I[bad] · coverCost.
  have h_cover_pointwise :
      ∀ W : Fin s → Finset X,
        (if IsBad ℋ s lambda_vec W then (1 : ℝ) else 0) * (1 / 2) ≤
        (if IsBad ℋ s lambda_vec W then (1 : ℝ) else 0) * coverCost ℋ s lambda_vec p W := by
    intro W
    by_cases h_bad : IsBad ℋ s lambda_vec W
    · -- Bad: use coverCost > 1/2 (now requires h_bad).
      have h_cover_lt :=
        coverCost_gt_half_of_not_psmall lambda_vec h_not_small h_H_nonempty W h_bad
          h_support (fun H hH x => (h_range H hH x).1) h_sum_ge_one
      rw [if_pos h_bad]; linarith
    · -- Not bad: indicator = 0, both sides = 0.
      rw [if_neg h_bad]; linarith
  -- Lift pointwise inequality to ProbXpJoint via monotonicity.
  have h_joint_le :
      ProbXpJoint q s
          (fun W => (if IsBad ℋ s lambda_vec W then (1 : ℝ) else 0) * (1 / 2)) ≤
      ProbXpJoint q s
          (fun W => (if IsBad ℋ s lambda_vec W then (1 : ℝ) else 0) * coverCost ℋ s lambda_vec p W) := by
    unfold ProbXpJoint
    apply Finset.sum_le_sum
    intro W _
    refine mul_le_mul_of_nonneg_right (h_cover_pointwise W) ?_
    apply Finset.prod_nonneg
    intro i _
    refine mul_nonneg ?_ ?_
    · exact pow_nonneg hq_pos.le _
    · exact pow_nonneg h_one_sub_q_nn _
  -- LHS = (1/2) · Pr[bad].
  have h_lhs_eq :
      ProbXpJoint q s
          (fun W => (if IsBad ℋ s lambda_vec W then (1 : ℝ) else 0) * (1 / 2)) =
      (1 / 2) *
        ProbXpJoint q s (fun W => if IsBad ℋ s lambda_vec W then (1 : ℝ) else 0) := by
    unfold ProbXpJoint
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro W _
    ring
  rw [h_lhs_eq] at h_joint_le
  -- The paper's key lemma bound (admitted): E[I[bad] · coverCost] ≤ 1/3.
  have h_star := Workspace.Axioms.LemKey.lem_key_bound p q ℋ s lambda_vec hp hq hq_le
    h_not_small h_H_nonempty h_range h_support h_sum_ge_one
  -- Combine: (1/2) · Pr[bad] ≤ E[bad · cost] ≤ 1/3, hence Pr[bad] ≤ 2/3.
  linarith [h_star]

end Workspace.Lemmas.KeyLemma
