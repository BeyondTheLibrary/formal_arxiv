import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Workspace.Definitions.ProbDistributions

open BigOperators
open Classical

namespace Workspace.Lemmas.UnionDistribution

open Workspace.Definitions.ProbDistributions

/-- Membership-reversal bijection: a function `W : Fin s → Finset X` is
equivalent to `m : X → Finset (Fin s)` via `m(x) = {i : x ∈ Wᵢ}`. -/
noncomputable def membershipReverse {X : Type} [Fintype X] [DecidableEq X] (s : ℕ) :
    (Fin s → Finset X) ≃ (X → Finset (Fin s)) where
  toFun W x := (Finset.univ : Finset (Fin s)).filter (fun i => x ∈ W i)
  invFun m i := (Finset.univ : Finset X).filter (fun x => i ∈ m x)
  left_inv W := by funext i; ext x; simp
  right_inv m := by funext x; ext i; simp

/-- **Lemma A** (linearity / sum-swap, fully proven). -/
lemma probXpJoint_sum_swap
    {X : Type} [Fintype X] [DecidableEq X]
    (q : ℝ) (s : ℕ) (A : Set (Finset X)) :
    ProbXpJoint q s
        (fun W : Fin s → Finset X =>
          if (Finset.univ.biUnion W) ∈ A then (1 : ℝ) else 0)
      = ∑ S : Finset X,
          if S ∈ A then
            ProbXpJoint q s
              (fun W : Fin s → Finset X =>
                if (Finset.univ.biUnion W) = S then (1 : ℝ) else 0)
          else 0 := by
  unfold ProbXpJoint
  have h_rewrite :
      (∑ S : Finset X, if S ∈ A then
        (∑ W : Fin s → Finset X,
          (if Finset.univ.biUnion W = S then (1 : ℝ) else 0) *
          ∏ i, q ^ (W i).card * (1 - q) ^ (Fintype.card X - (W i).card))
       else 0) =
      ∑ S : Finset X, ∑ W : Fin s → Finset X,
        ((if S ∈ A then (1 : ℝ) else 0) *
         (if Finset.univ.biUnion W = S then (1 : ℝ) else 0)) *
        ∏ i, q ^ (W i).card * (1 - q) ^ (Fintype.card X - (W i).card) := by
    apply Finset.sum_congr rfl
    intro S _
    by_cases hSA : S ∈ A
    · rw [if_pos hSA]
      apply Finset.sum_congr rfl
      intro W _
      show (if Finset.univ.biUnion W = S then (1 : ℝ) else 0) *
           (∏ i, q ^ (W i).card * (1 - q) ^ (Fintype.card X - (W i).card)) =
           ((if S ∈ A then (1 : ℝ) else 0) *
            (if Finset.univ.biUnion W = S then (1 : ℝ) else 0)) *
           (∏ i, q ^ (W i).card * (1 - q) ^ (Fintype.card X - (W i).card))
      rw [if_pos hSA, one_mul]
    · rw [if_neg hSA]
      symm
      apply Finset.sum_eq_zero
      intro W _
      show ((if S ∈ A then (1 : ℝ) else 0) *
            (if Finset.univ.biUnion W = S then (1 : ℝ) else 0)) *
           (∏ i, q ^ (W i).card * (1 - q) ^ (Fintype.card X - (W i).card)) = 0
      rw [if_neg hSA, zero_mul, zero_mul]
  rw [h_rewrite, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro W _
  rw [← Finset.sum_mul]
  congr 1
  rw [Finset.sum_eq_single (Finset.univ.biUnion W)]
  · rw [if_pos rfl, mul_one]
  · intro S _ hS_ne
    have h_ne : ¬ Finset.univ.biUnion W = S := fun h => hS_ne h.symm
    rw [if_neg h_ne, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Lemma B** (per-element factorisation, the deep content).

# References

The underlying probabilistic fact — that the union of `s` independent Bernoulli
random subsets is itself a Bernoulli random subset with parameter
`1 − (1−q)^s` — is a classical result from elementary probability theory and
appears in standard textbook treatments of Bernoulli trials, independence, and
product measures. References:

* M. Mitzenmacher and E. Upfal, *Probability and Computing: Randomization and
  Probabilistic Techniques in Algorithms and Data Analysis*, 2nd ed.,
  Cambridge Univ. Press, 2017. Chapter 1 (basic probability and Bernoulli trials).
* W. Feller, *An Introduction to Probability Theory and Its Applications*,
  Vol. 1, 3rd ed., Wiley, 1968. Chapters on Bernoulli trials and independence.
* G. Grimmett and D. Stirzaker, *Probability and Random Processes*, 3rd ed.,
  Oxford Univ. Press, 2001. Chapter on independence and product spaces.
* N. Alon and J. Spencer, *The Probabilistic Method*, 4th ed., Wiley, 2016.
  Used throughout in the random subset / Erdős–Rényi context (`G(n, p)`).
* S. Janson, T. Łuczak and A. Ruciński, *Random Graphs*, Wiley, 2000.
  Standard treatment of Bernoulli random subsets and their unions.

In the source paper (the application here), this fact is invoked without proof
as the comment "Note that the set `⋃ W_i` has the same distribution as
`X_{q̃}` where `q̃ = 1 − (1 − q)^s`" in §3.3 (line preceding eq. 3.7 of the
selector-process proof).

# Statement

For a fixed subset `S ⊆ X`, the joint probability that `⋃ Wᵢ = S` equals the
Bernoulli weight at parameter `1 - (1-q)^s`:

`ProbXpJoint q s [⋃ W = S] = (1-(1-q)^s)^|S| · ((1-q)^s)^(|X|-|S|)`.

**Proof outline (per-element)**:

1. Apply the `membershipReverse` bijection (defined above): each
   `W : Fin s → Finset X` corresponds to `m : X → Finset (Fin s)` with
   `m(x) = {i : x ∈ Wᵢ}`.

2. Reformulate the joint Bernoulli weight as a per-element product:
   `∏ᵢ q^|Wᵢ|·(1-q)^(|X|-|Wᵢ|) = ∏ₓ q^|m(x)|·(1-q)^(s-|m(x)|)`. Both equal
   `q^N · (1-q)^(s·|X| − N)` where `N = ∑ᵢ |Wᵢ| = ∑ₓ |m(x)|` is the total
   number of pairs `(i, x)` with `x ∈ Wᵢ` (count identity by double counting).

3. Translate the constraint `⋃ Wᵢ = S` to `m ∈ piFinset (T_per_x)` where
   `T_per_x x = if x ∈ S then {T : T ≠ ∅} else {∅}`.

4. Apply `Finset.prod_univ_sum`:
   `∏ₓ ∑_{T ∈ T_per_x x} q^|T|(1-q)^(s-|T|) = ∑_{m ∈ piFinset T_per_x} ∏ₓ ...`

5. Per-element evaluation:
   - `x ∈ S`: `∑_{T ≠ ∅} q^|T|(1-q)^(s-|T|) = (q+(1-q))^s - (1-q)^s = 1-(1-q)^s`
     (via `Fintype.sum_pow_mul_eq_add_pow` minus the empty term).
   - `x ∉ S`: only `T = ∅` contributes `(1-q)^s`.

6. Combine via `Finset.prod_const` + `Finset.prod_ite` to get
   `(1-(1-q)^s)^|S| · ((1-q)^s)^(|X|-|S|)`.

The full Lean implementation combines the bijection, weight reformulation
(via the per-element decomposition `q^|F|·(1-q)^(|β|-|F|) = ∏ y, if y ∈ F
then q else (1-q)` together with `Finset.prod_comm`), constraint
translation, and per-element evaluation. The required Mathlib pieces
used here are `Fintype.sum_equiv`, `Finset.prod_univ_sum`, and
`Fintype.sum_pow_mul_eq_add_pow`.
-/
lemma probXpJoint_singleton
    {X : Type} [Fintype X] [DecidableEq X]
    (q : ℝ) (s : ℕ) (S : Finset X) :
    ProbXpJoint q s
        (fun W : Fin s → Finset X =>
          if (Finset.univ.biUnion W) = S then (1 : ℝ) else 0)
      = (1 - (1 - q) ^ s) ^ S.card *
        ((1 - q) ^ s) ^ (Fintype.card X - S.card) := by
  -- We work with the bijection `e := membershipReverse s : (Fin s → Finset X) ≃ (X → Finset (Fin s))`
  -- where `(e W) x = {i : x ∈ W i}` (the membership-reversal map).
  -- Key per-element identity: under the bijection, the joint Bernoulli weight factors over `X`,
  -- and the constraint `⋃ W = S` becomes `∀ x, (e W) x ≠ ∅ ↔ x ∈ S`.
  set e : (Fin s → Finset X) ≃ (X → Finset (Fin s)) := membershipReverse s with he_def
  -- Per-element weight function.
  set w : ℕ → ℝ := fun k => q ^ k * (1 - q) ^ (s - k) with hw_def
  -- Per-element predicate-weighted summand: (predicate_x T) * weight(|T|).
  set wx : X → Finset (Fin s) → ℝ :=
    fun x T => (if (T = ∅ ↔ x ∉ S) then (1 : ℝ) else 0) * w T.card with hwx_def
  -- Step 1. Unfold ProbXpJoint and reorganize the sum via the bijection.
  unfold ProbXpJoint
  -- Step 2. The union condition under the bijection. For W ↔ m via e:
  --   `Finset.univ.biUnion W = S ↔ ∀ x, m x = ∅ ↔ x ∉ S`.
  have h_union_iff : ∀ W : Fin s → Finset X,
      (Finset.univ.biUnion W = S) ↔ (∀ x, (e W) x = ∅ ↔ x ∉ S) := by
    intro W
    constructor
    · intro h x
      have hmem : ∀ y : X, y ∈ Finset.univ.biUnion W ↔ ∃ i, y ∈ W i := by
        intro y
        simp [Finset.mem_biUnion]
      have hSx : x ∈ S ↔ ∃ i, x ∈ W i := by
        rw [← h]; exact hmem x
      simp only [he_def, membershipReverse, Equiv.coe_fn_mk]
      rw [Finset.eq_empty_iff_forall_notMem]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hall hxS
        obtain ⟨i, hi⟩ := hSx.mp hxS
        exact hall i hi
      · intro hxnotS i hi
        exact hxnotS (hSx.mpr ⟨i, hi⟩)
    · intro hall
      ext y
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      have hy := hall y
      simp only [he_def, membershipReverse, Equiv.coe_fn_mk] at hy
      rw [Finset.eq_empty_iff_forall_notMem] at hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      constructor
      · rintro ⟨i, hi⟩
        by_contra hyS
        exact (hy.mpr hyS i) hi
      · intro hyS
        by_contra hno
        push_neg at hno
        have : ∀ i, y ∉ W i := hno
        exact (hy.mp this) hyS
  -- Step 3. Per-element weight factorization (deep step):
  --   `∏ i, q^|W i| · (1-q)^(|X| - |W i|) = ∏ x, q^|m x| · (1-q)^(s - |m x|)` where m = e W.
  -- We rewrite each factor as `∏ x, if x ∈ W i then q else (1-q)` and swap products.
  have h_weight_factor : ∀ W : Fin s → Finset X,
      (∏ i : Fin s, q ^ (W i).card * (1 - q) ^ (Fintype.card X - (W i).card))
        = ∏ x : X, w ((e W) x).card := by
    intro W
    -- Helper: for any Finset F ⊆ Finset.univ over a fintype β, with F.card and the
    -- per-element product representation:
    -- `q^|F| · (1-q)^(|β| - |F|) = ∏ y, if y ∈ F then q else (1-q)`.
    have h_pointwise : ∀ {β : Type} [Fintype β] [DecidableEq β] (F : Finset β),
        q ^ F.card * (1 - q) ^ (Fintype.card β - F.card)
          = ∏ y : β, if y ∈ F then q else (1 - q) := by
      intro β _ _ F
      rw [show (∏ y : β, if y ∈ F then q else (1 - q))
            = (∏ y ∈ (Finset.univ : Finset β).filter (· ∈ F), q)
              * ∏ y ∈ (Finset.univ : Finset β).filter (fun y => ¬ y ∈ F), (1 - q) from
          Finset.prod_ite (fun _ => q) (fun _ => 1 - q)]
      have hF : (Finset.univ : Finset β).filter (· ∈ F) = F := by ext; simp
      have hFc : (Finset.univ : Finset β).filter (fun y => ¬ y ∈ F) = (Finset.univ : Finset β) \ F := by
        ext; simp
      rw [hF, hFc, Finset.prod_const, Finset.prod_const]
      have hcard : ((Finset.univ : Finset β) \ F).card = Fintype.card β - F.card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ F)]
        rfl
      rw [hcard]
    -- Apply h_pointwise to LHS for each i.
    rw [show (∏ i : Fin s, q ^ (W i).card * (1 - q) ^ (Fintype.card X - (W i).card))
          = ∏ i : Fin s, ∏ x : X, if x ∈ W i then q else (1 - q) from
        Finset.prod_congr rfl (fun i _ => h_pointwise (W i))]
    -- Swap products.
    rw [Finset.prod_comm]
    -- Apply h_pointwise to RHS for each x.
    show (∏ x : X, ∏ i : Fin s, if x ∈ W i then q else (1 - q))
          = ∏ x : X, w ((e W) x).card
    apply Finset.prod_congr rfl
    intro x _
    rw [hw_def]
    show (∏ i : Fin s, if x ∈ W i then q else (1 - q))
          = q ^ ((e W) x).card * (1 - q) ^ (s - ((e W) x).card)
    have hcard_fin : Fintype.card (Fin s) = s := Fintype.card_fin s
    have hkey : (∏ i : Fin s, if x ∈ W i then q else (1 - q))
        = q ^ ((e W) x).card * (1 - q) ^ (Fintype.card (Fin s) - ((e W) x).card) := by
      rw [h_pointwise ((e W) x)]
      apply Finset.prod_congr rfl
      intro i _
      simp only [he_def, membershipReverse, Equiv.coe_fn_mk, Finset.mem_filter, Finset.mem_univ,
        true_and]
    rw [hkey, hcard_fin]
  -- Step 4. Indicator for union = S becomes a product over X.
  have h_indicator_prod : ∀ W : Fin s → Finset X,
      (if Finset.univ.biUnion W = S then (1 : ℝ) else 0)
        = ∏ x : X, if ((e W) x = ∅ ↔ x ∉ S) then (1 : ℝ) else 0 := by
    intro W
    by_cases h : Finset.univ.biUnion W = S
    · rw [if_pos h]
      have hall := (h_union_iff W).mp h
      symm
      apply Finset.prod_eq_one
      intro x _
      rw [if_pos (hall x)]
    · rw [if_neg h]
      symm
      have hnotall : ¬ (∀ x, (e W) x = ∅ ↔ x ∉ S) :=
        fun hall => h ((h_union_iff W).mpr hall)
      have hexists : ∃ x, ¬ ((e W) x = ∅ ↔ x ∉ S) := by
        by_contra hno
        push_neg at hno
        exact hnotall hno
      obtain ⟨x, hx⟩ := hexists
      apply Finset.prod_eq_zero (Finset.mem_univ x)
      rw [if_neg hx]
  -- Step 5. Substitute the indicator product and weight factorization.
  have h_summand_factor : ∀ W : Fin s → Finset X,
      (if Finset.univ.biUnion W = S then (1 : ℝ) else 0) *
        (∏ i : Fin s, q ^ (W i).card * (1 - q) ^ (Fintype.card X - (W i).card))
        = ∏ x : X, wx x ((e W) x) := by
    intro W
    rw [h_indicator_prod W, h_weight_factor W, ← Finset.prod_mul_distrib]
  -- Step 6. Apply the bijection to switch sum from W to m := e W.
  rw [show (∑ W : Fin s → Finset X,
        (if Finset.univ.biUnion W = S then (1 : ℝ) else 0) *
        ∏ i : Fin s, q ^ (W i).card * (1 - q) ^ (Fintype.card X - (W i).card))
      = ∑ W : Fin s → Finset X, ∏ x : X, wx x ((e W) x) from
        Finset.sum_congr rfl (fun W _ => h_summand_factor W)]
  -- Step 7. Switch sum-over-W to sum-over-m using the equiv.
  rw [show (∑ W : Fin s → Finset X, ∏ x : X, wx x ((e W) x))
        = ∑ m : X → Finset (Fin s), ∏ x : X, wx x (m x) from
        Fintype.sum_equiv e _ _ (fun W => rfl)]
  -- Step 8. Convert sum over m : X → Finset (Fin s) into sum over piFinset.
  -- Since `Finset (Fin s)` is fintype, `m : X → Finset (Fin s)` ranges over all functions,
  -- which equals `piFinset (fun _ => univ)`.
  have h_piFinset_univ :
      (Finset.univ : Finset (X → Finset (Fin s)))
        = Fintype.piFinset (fun _ : X => (Finset.univ : Finset (Finset (Fin s)))) := by
    ext m
    simp [Fintype.mem_piFinset]
  rw [show (∑ m : X → Finset (Fin s), ∏ x : X, wx x (m x))
        = ∑ m ∈ Fintype.piFinset (fun _ : X => (Finset.univ : Finset (Finset (Fin s)))),
            ∏ x : X, wx x (m x) by rw [← h_piFinset_univ]]
  -- Step 9. Apply prod_univ_sum: `∑_m ∏_x f(x, m x) = ∏_x ∑_T f(x, T)` (in reverse).
  rw [← Finset.prod_univ_sum (fun _ : X => (Finset.univ : Finset (Finset (Fin s))))
        (fun x T => wx x T)]
  -- Step 10. Per-element evaluation: split by `x ∈ S`.
  -- For x ∈ S: ∑_T (if (T=∅ ↔ False) then 1 else 0) * w |T| = ∑_{T ≠ ∅} w |T| = 1 - (1-q)^s.
  -- For x ∉ S: ∑_T (if (T=∅ ↔ True) then 1 else 0) * w |T| = w 0 = (1-q)^s.
  have h_eval_in : ∀ x ∈ S, (∑ T : Finset (Fin s), wx x T) = 1 - (1 - q) ^ s := by
    intro x hxS
    -- For x ∈ S, `(T = ∅ ↔ x ∉ S)` simplifies to `T ≠ ∅`.
    have hsimp : ∀ T : Finset (Fin s), (T = ∅ ↔ x ∉ S) ↔ T ≠ ∅ := by
      intro T
      constructor
      · intro h hT
        exact (h.mp hT) hxS
      · intro hT
        constructor
        · intro hT_eq; exact absurd hT_eq hT
        · intro hxnS; exact absurd hxS hxnS
    simp only [hwx_def, hsimp]
    -- Now ∑_T (if T ≠ ∅ then 1 else 0) * w |T| = (∑_T w |T|) - w 0.
    have h1 : (∑ T : Finset (Fin s), (if T ≠ ∅ then (1 : ℝ) else 0) * w T.card)
        = (∑ T : Finset (Fin s), w T.card) - w 0 := by
      rw [show (∑ T : Finset (Fin s), w T.card)
            = w 0 + ∑ T ∈ (Finset.univ : Finset (Finset (Fin s))).erase ∅, w T.card by
            rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (∅ : Finset (Fin s)))]
            simp]
      rw [add_sub_cancel_left]
      rw [show (∑ T : Finset (Fin s), (if T ≠ ∅ then (1 : ℝ) else 0) * w T.card)
            = ∑ T ∈ (Finset.univ : Finset (Finset (Fin s))).erase ∅, w T.card by
            rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (∅ : Finset (Fin s)))]
            simp only [ne_eq, not_true_eq_false, if_false, zero_mul, add_zero]
            apply Finset.sum_congr rfl
            intro T hT
            rw [Finset.mem_erase] at hT
            rw [if_pos hT.1, one_mul]]
    rw [h1]
    -- ∑_T w |T| = (q + (1-q))^s = 1^s = 1.
    have h2 : (∑ T : Finset (Fin s), w T.card) = (q + (1 - q)) ^ s := by
      simp only [hw_def]
      have := Fintype.sum_pow_mul_eq_add_pow (Fin s) q (1 - q)
      simp only [Fintype.card_fin] at this
      exact this
    rw [h2]
    have hsum1 : q + (1 - q) = 1 := by ring
    rw [hsum1, one_pow]
    -- w 0 = (1-q)^s
    simp only [hw_def, pow_zero, one_mul, Nat.sub_zero]
  have h_eval_notin : ∀ x ∉ S, (∑ T : Finset (Fin s), wx x T) = (1 - q) ^ s := by
    intro x hxS
    -- For x ∉ S, `(T = ∅ ↔ x ∉ S)` simplifies to `T = ∅`.
    have hsimp : ∀ T : Finset (Fin s), (T = ∅ ↔ x ∉ S) ↔ T = ∅ := by
      intro T
      constructor
      · intro h; exact h.mpr hxS
      · intro hT
        constructor
        · intro _; exact hxS
        · intro _; exact hT
    simp only [hwx_def, hsimp]
    -- Sum over T of (if T = ∅ then 1 else 0) * w |T| = w 0.
    rw [show (∑ T : Finset (Fin s), (if T = ∅ then (1 : ℝ) else 0) * w T.card) = w 0 by
        rw [Finset.sum_eq_single (∅ : Finset (Fin s))]
        · rw [if_pos rfl, one_mul, Finset.card_empty]
        · intro T _ hT_ne
          rw [if_neg hT_ne, zero_mul]
        · intro hempty
          exact absurd (Finset.mem_univ _) hempty]
    simp only [hw_def, pow_zero, one_mul, Nat.sub_zero]
  -- Step 11. Combine via prod_ite to split the product over X by the predicate `x ∈ S`.
  have h_prod_split :
      (∏ x : X, ∑ T : Finset (Fin s), wx x T)
        = (∏ x ∈ S, (1 - (1 - q) ^ s)) * ∏ x ∈ (Finset.univ : Finset X) \ S, (1 - q) ^ s := by
    -- Rewrite each factor depending on whether x ∈ S, then split.
    have hsplit :
      ∀ x : X, (∑ T : Finset (Fin s), wx x T)
          = if x ∈ S then 1 - (1 - q) ^ s else (1 - q) ^ s := by
      intro x
      by_cases hxS : x ∈ S
      · rw [if_pos hxS]; exact h_eval_in x hxS
      · rw [if_neg hxS]; exact h_eval_notin x hxS
    rw [show (∏ x : X, ∑ T : Finset (Fin s), wx x T)
          = ∏ x : X, if x ∈ S then 1 - (1 - q) ^ s else (1 - q) ^ s from
        Finset.prod_congr rfl (fun x _ => hsplit x)]
    rw [Finset.prod_ite (fun x => 1 - (1 - q) ^ s) (fun x => (1 - q) ^ s)]
    congr 1
    · rw [show ((Finset.univ : Finset X).filter (fun x => x ∈ S)) = S by
            ext x; simp]
    · rw [show ((Finset.univ : Finset X).filter (fun x => ¬ x ∈ S)) = (Finset.univ : Finset X) \ S by
            ext x; simp]
  rw [h_prod_split, Finset.prod_const, Finset.prod_const]
  -- Cardinality: |univ \ S| = |X| - |S|.
  have hcard : ((Finset.univ : Finset X) \ S).card = Fintype.card X - S.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    rfl
  rw [hcard]

/-- **Distribution of `⋃_{i=1}^s W_i` where `W_i ∼ X_q` are independent**
(paper §3.3, the "Note that …" line).

# Proof

Structural, reducing to two helper lemmas:
1. `probXpJoint_sum_swap` (proven) — split by exact union value `S`.
2. `probXpJoint_singleton` (proven) — per-element Bernoulli factorisation.
-/
theorem union_distribution_eq
    {X : Type} [Fintype X] [DecidableEq X]
    (q : ℝ) (s : ℕ) (A : Set (Finset X))
    (_hq_nonneg : 0 ≤ q) (_hq_le_one : q ≤ 1) :
    ProbXpJoint q s
        (fun W : Fin s → Finset X =>
          if (Finset.univ.biUnion W) ∈ A then (1 : ℝ) else 0)
      = ProbXp (1 - (1 - q) ^ s) A := by
  rw [probXpJoint_sum_swap q s A]
  unfold ProbXp
  apply Finset.sum_congr rfl
  intro S _hS
  by_cases h_in : S ∈ A
  · rw [if_pos h_in, if_pos h_in]
    have h_complement : (1 : ℝ) - (1 - (1 - q) ^ s) = (1 - q) ^ s := by ring
    rw [h_complement]
    exact probXpJoint_singleton q s S
  · rw [if_neg h_in, if_neg h_in]

end Workspace.Lemmas.UnionDistribution
