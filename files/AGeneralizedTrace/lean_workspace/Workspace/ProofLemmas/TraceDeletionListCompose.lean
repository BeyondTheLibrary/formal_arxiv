import Mathlib

/-!
# List-level model of independent bit-deletion and its composition

This file develops a *reindexing-free* list-level model of the post-deletion
process used by `TraceDeletionKernel.traceDelete`, together with the key
composition lemma that drives the kernel-composition law.

The post-deletion process keeps each bit of a list independently.  We model the
per-position keep/drop decisions as a `List Bool` `d` of the same length as the
input list `l`; `keepWith l d` is the sublist of `l` at the positions where `d`
is `true`.  Two independent stages compose: the second stage's decision list
`d₂` (which has length `(keepWith l d₁).length`) is *merged* into the `true`
positions of the first stage's decision list `d₁`, producing a single decision
list `mergeDecisions d₁ d₂` of length `l.length` such that

    keepWith (keepWith l d₁) d₂ = keepWith l (mergeDecisions d₁ d₂).

This is the list-level analogue of the sublist-rank reindexing, made completely
explicit and proved sorry-free by induction on `d₁`.  It avoids the random
`Fin`-length reindexing obstacle entirely.
-/

namespace TraceDeletionListCompose

/-- Keep the elements of `l` at positions where the decision list `d` is `true`.
Pairs `l` with `d` position-wise (via `List.zip`) and keeps the `true` ones. -/
def keepWith (l : List Bool) (d : List Bool) : List Bool :=
  (l.zip d).filterMap (fun p => if p.2 then some p.1 else none)

@[simp] lemma keepWith_nil_left (d : List Bool) : keepWith [] d = [] := by
  simp [keepWith]

@[simp] lemma keepWith_nil_right (l : List Bool) : keepWith l [] = [] := by
  simp [keepWith]

@[simp] lemma keepWith_cons_true (a : Bool) (l : List Bool) (d : List Bool) :
    keepWith (a :: l) (true :: d) = a :: keepWith l d := by
  simp [keepWith]

@[simp] lemma keepWith_cons_false (a : Bool) (l : List Bool) (d : List Bool) :
    keepWith (a :: l) (false :: d) = keepWith l d := by
  simp [keepWith]

/-- Merge a second-stage decision list `d₂` into the `true`-positions of a
first-stage decision list `d₁`.  At a `false` of `d₁` the position is already
dropped, so it stays `false` and `d₂` is not consumed; at a `true` of `d₁` the
position survived stage one, so the next bit of `d₂` decides its fate. -/
def mergeDecisions : List Bool → List Bool → List Bool
  | [], _ => []
  | false :: d₁, d₂ => false :: mergeDecisions d₁ d₂
  | true :: d₁, [] => false :: mergeDecisions d₁ []
  | true :: d₁, b :: d₂ => b :: mergeDecisions d₁ d₂

@[simp] lemma mergeDecisions_nil_left (d₂ : List Bool) :
    mergeDecisions [] d₂ = [] := rfl

@[simp] lemma mergeDecisions_false (d₁ d₂ : List Bool) :
    mergeDecisions (false :: d₁) d₂ = false :: mergeDecisions d₁ d₂ := rfl

@[simp] lemma mergeDecisions_true_nil (d₁ : List Bool) :
    mergeDecisions (true :: d₁) [] = false :: mergeDecisions d₁ [] := rfl

@[simp] lemma mergeDecisions_true_cons (d₁ : List Bool) (b : Bool) (d₂ : List Bool) :
    mergeDecisions (true :: d₁) (b :: d₂) = b :: mergeDecisions d₁ d₂ := rfl

/-- `mergeDecisions` preserves the length of the first-stage decision list. -/
@[simp] lemma length_mergeDecisions (d₁ d₂ : List Bool) :
    (mergeDecisions d₁ d₂).length = d₁.length := by
  induction d₁ generalizing d₂ with
  | nil => simp
  | cons a d₁ ih =>
    cases a with
    | false => simp [ih]
    | true =>
      cases d₂ with
      | nil => simp [ih]
      | cons b d₂ => simp [ih]

/-- Merging an empty second-stage decision list drops everything: the resulting
decision list keeps no position. -/
lemma keepWith_mergeDecisions_nil (l d₁ : List Bool) :
    keepWith l (mergeDecisions d₁ []) = [] := by
  induction l generalizing d₁ with
  | nil => simp
  | cons a l ih =>
    cases d₁ with
    | nil => simp
    | cons b₁ d₁ =>
      cases b₁ with
      | false => simp only [mergeDecisions_false, keepWith_cons_false]; exact ih d₁
      | true => simp only [mergeDecisions_true_nil, keepWith_cons_false]; exact ih d₁

/-- **List-level composition law (reindexing-free).**
Applying the keep operation twice — first with `d₁`, then with `d₂` on the
result — equals applying it once with the merged decision list.  Proved by a
clean structural induction on `d₁`, with no `Fin`-length reindexing. -/
theorem keepWith_keepWith (l d₁ d₂ : List Bool) :
    keepWith (keepWith l d₁) d₂ = keepWith l (mergeDecisions d₁ d₂) := by
  induction l generalizing d₁ d₂ with
  | nil => simp
  | cons a l ih =>
    cases d₁ with
    | nil => simp
    | cons b₁ d₁ =>
      cases b₁ with
      | false =>
        simp only [keepWith_cons_false, mergeDecisions_false]
        rw [ih]
      | true =>
        cases d₂ with
        | nil =>
          simp only [keepWith_cons_true, keepWith_nil_right, mergeDecisions_true_nil,
            keepWith_cons_false]
          exact (keepWith_mergeDecisions_nil l d₁).symm
        | cons b₂ d₂ =>
          cases b₂ with
          | false =>
            simp only [keepWith_cons_true, keepWith_cons_false, mergeDecisions_true_cons]
            rw [ih]
          | true =>
            simp only [keepWith_cons_true, mergeDecisions_true_cons]
            rw [ih]

/-- **Bridge lemma.**  The list-level `keepWith` with a decision list materialised
from a per-position mask `m : Fin l.length → Bool` (via `List.ofFn m`) equals the
`finRange`-indexed `filterMap` that the kernel's `keep` operation uses.  This is the
key step connecting the reindexing-free list model to the `Fin`-mask kernel; it is
proved by `List.ext_getElem?`, sidestepping the `motive is not type correct`
obstruction of a direct dependent rewrite. -/
lemma keepWith_ofFn (l : List Bool) (m : Fin l.length → Bool) :
    keepWith l (List.ofFn m) =
      (List.finRange l.length).filterMap (fun i => if m i then some l[i] else none) := by
  unfold keepWith
  have h : l.zip (List.ofFn m)
      = (List.finRange l.length).map (fun i => (l[i], m i)) := by
    apply List.ext_getElem?
    intro i
    rw [List.zip_eq_zipWith, List.getElem?_zipWith', List.getElem?_map,
      List.getElem?_ofFn]
    rcases lt_or_ge i l.length with hi | hi
    · rw [List.getElem?_eq_getElem hi,
        List.getElem?_eq_getElem (by simpa using hi : i < (List.finRange l.length).length)]
      simp [hi, List.getElem_finRange]
    · rw [List.getElem?_eq_none hi,
        List.getElem?_eq_none (by simpa using hi : (List.finRange l.length).length ≤ i)]
      simp [Nat.not_lt.mpr hi]
  rw [h, List.filterMap_map]
  rfl

/-! ### Weight composition over decision lists (toward the summed kernel law)

We now develop the multiplicative-weight side of the two-stage composition at the
*list* level, again avoiding any `Fin`-length reindexing.  A per-position Bernoulli
weight is a function `w : Bool → M` into a commutative monoid `M`; the weight of a
decision list is the product of the per-position weights.  The central fact is that
the weight of a *merged* decision list factors into a product over the dead
(first-stage `false`) positions and a product over the second-stage decision bits —
mirroring `keepWith`'s structural recursion exactly. -/

section Weights

variable {M : Type*} [CommMonoid M]

/-- The multiplicative weight of a decision list under a per-position weight `w`. -/
def dWeight (w : Bool → M) (d : List Bool) : M := (d.map w).prod

@[simp] lemma dWeight_nil (w : Bool → M) : dWeight w [] = 1 := by simp [dWeight]

@[simp] lemma dWeight_cons (w : Bool → M) (b : Bool) (d : List Bool) :
    dWeight w (b :: d) = w b * dWeight w d := by simp [dWeight]

/-- Number of `false` entries of a decision list (the dead first-stage positions). -/
def deadCount : List Bool → ℕ
  | [] => 0
  | false :: d => deadCount d + 1
  | true :: d => deadCount d

@[simp] lemma deadCount_nil : deadCount [] = 0 := rfl
@[simp] lemma deadCount_false (d : List Bool) :
    deadCount (false :: d) = deadCount d + 1 := rfl
@[simp] lemma deadCount_true (d : List Bool) :
    deadCount (true :: d) = deadCount d := rfl

/-- **Merged-decision weight factorization (exact-length stage two).**  Under a
*single-stage* per-position weight `w`, when the second-stage decision list `d₂`
covers *exactly* the survivors of `d₁` (`d₂.length = d₁.count true`), the weight of
`mergeDecisions d₁ d₂` splits as `w false` raised to the number of dead (`false`)
first-stage positions, times the weight of `d₂`.  Every `false` of `d₁` contributes
`w false` (dead, consumes no `d₂` bit); every `true` of `d₁` consumes the next bit
of `d₂` (none are left over since the lengths match), contributing `dWeight w d₂`. -/
lemma dWeight_mergeDecisions (w : Bool → M) (d₁ d₂ : List Bool)
    (hlen : d₂.length = d₁.count true) :
    dWeight w (mergeDecisions d₁ d₂)
      = (w false) ^ deadCount d₁ * dWeight w d₂ := by
  induction d₁ generalizing d₂ with
  | nil =>
    simp only [List.count_nil] at hlen
    simp [List.length_eq_zero_iff.mp hlen]
  | cons a d₁ ih =>
    cases a with
    | false =>
      have hcount : List.count true (false :: d₁) = List.count true d₁ := by simp
      rw [hcount] at hlen
      simp only [mergeDecisions_false, dWeight_cons, deadCount_false, pow_succ]
      rw [ih d₂ hlen]
      ac_rfl
    | true =>
      have hcount : List.count true (true :: d₁) = List.count true d₁ + 1 := by simp
      rw [hcount] at hlen
      cases d₂ with
      | nil => simp at hlen
      | cons b d₂ =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        simp only [mergeDecisions_true_cons, dWeight_cons, deadCount_true]
        rw [ih d₂ hlen]
        ac_rfl

/-- A decision-list weight is determined by the bit *counts*: the weight is
`w true` to the number of `true`s times `w false` to the number of `false`s. -/
lemma dWeight_eq_pow_counts (w : Bool → M) (d : List Bool) :
    dWeight w d = (w true) ^ d.count true * (w false) ^ d.count false := by
  induction d with
  | nil => simp
  | cons a d ih =>
    cases a with
    | false =>
      have ht : (false :: d).count true = d.count true := by simp
      have hf : (false :: d).count false = d.count false + 1 := by simp
      rw [dWeight_cons, ih, ht, hf, pow_succ]
      ac_rfl
    | true =>
      have ht : (true :: d).count true = d.count true + 1 := by simp
      have hf : (true :: d).count false = d.count false := by simp
      rw [dWeight_cons, ih, ht, hf, pow_succ]
      ac_rfl

end Weights

/-- **Surviving-weight two-stage composition (list level).**  When the second-stage
decision list `d₂` covers exactly the survivors of `d₁` (`d₂.length = d₁.count true`),
the merged *single-stage* weight equals the dead-position contribution
`(w false)^{deadCount d₁}` times the second-stage weight `dWeight w d₂`.  This is the
list-level engine of part (c): combined with the per-coordinate
`TraceDeletionKernel.factor_keep_compose` (`w₁ true · w₂ true = w true`), the
*surviving* bits of a two-stage process compose to the single-stage rate `q`, and the
dead positions are isolated into the explicit `(w false)^{deadCount d₁}` factor.

The remaining (deliberately not closed) gap to the full kernel law
`(traceDelete q₁ t).bind (traceDelete q₂) = traceDelete q t` is exactly the
dead-position reconciliation: a stage-one-dead position carries two-stage weight
`w₁ false = q₁`, whereas the single-stage rate is `w false = q`; matching them
requires the *outer* marginalization over the output trace — summing each dead
position's (absent) stage-two bit, whose total mass is one — which lives at the PMF
`tsum` level over the variable-length intermediate trace, not at this list level. -/
lemma dWeight_compose_survivors {M : Type*} [CommMonoid M]
    (w₁ w₂ w : Bool → M) (d₁ d₂ : List Bool)
    (hsurv : w₁ true * w₂ true = w true)
    (hlen : d₂.length = d₁.count true) :
    dWeight w (mergeDecisions d₁ d₂)
      = (w false) ^ deadCount d₁ * (w₁ true) ^ d₂.count true * (w₂ true) ^ d₂.count true
        * (w false) ^ d₂.count false := by
  rw [dWeight_mergeDecisions w d₁ d₂ hlen, dWeight_eq_pow_counts w d₂, ← hsurv,
    mul_pow]
  ac_rfl

/-! ### Invertibility of `mergeDecisions` (toward the PMF marginalization)

The list-level composition `mergeDecisions d₁ ·` is *injective* on second-stage
decision lists of exact survivor length: the original `d₂` can be recovered from
`mergeDecisions d₁ d₂` by reading off `d`'s bits at the `true`-positions of `d₁`.
This is the combinatorial engine the PMF-level marginalization needs to reindex a
double sum over `(m₁, m₂)` against a single sum over the merged mask: the survivor
sub-mask `m₂` is determined by `m₁` and the merged mask, while the dead positions
of `m₁` carry no `m₂` bit (their stage-two mass marginalizes to one). -/

/-- Recover the second-stage decision list from a merged decision list `d`
relative to a first-stage decision list `d₁`: read off the bit of `d` at each
`true`-position of `d₁`, in order. -/
def unmerge : List Bool → List Bool → List Bool
  | [], _ => []
  | false :: d₁, d => unmerge d₁ d.tail
  | true :: d₁, d => d.headD false :: unmerge d₁ d.tail

/-- **`mergeDecisions` is injective in its second argument** (on lists of exact
survivor length): `unmerge d₁` left-inverts `mergeDecisions d₁ ·`. -/
theorem unmerge_mergeDecisions (d₁ d₂ : List Bool) (hlen : d₂.length = d₁.count true) :
    unmerge d₁ (mergeDecisions d₁ d₂) = d₂ := by
  induction d₁ generalizing d₂ with
  | nil =>
    simp only [List.count_nil] at hlen
    rw [List.length_eq_zero_iff.mp hlen]; rfl
  | cons a d₁ ih =>
    cases a with
    | false =>
      have hc : List.count true (false :: d₁) = List.count true d₁ := by simp
      rw [hc] at hlen
      simp only [mergeDecisions_false, unmerge]
      exact ih d₂ hlen
    | true =>
      have hc : List.count true (true :: d₁) = List.count true d₁ + 1 := by simp
      rw [hc] at hlen
      cases d₂ with
      | nil => simp at hlen
      | cons b d₂ =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        simp only [mergeDecisions_true_cons, unmerge, List.headD_cons, List.tail_cons]
        rw [ih d₂ hlen]

/-- `unmerge` produces a list of exactly survivor length (`d₁.count true`). -/
theorem length_unmerge (d₁ d : List Bool) :
    (unmerge d₁ d).length = d₁.count true := by
  induction d₁ generalizing d with
  | nil => simp [unmerge]
  | cons a d₁ ih =>
    cases a with
    | false => simp only [unmerge, List.count_cons]; rw [ih d.tail]; simp
    | true => simp only [unmerge, List.length_cons, List.count_cons]; rw [ih d.tail]; simp

/-- The survivor length of `keepWith l d` (when `d.length = l.length`) is the
number of `true`s in `d`.  This is the exact-length hypothesis feeding
`dWeight_mergeDecisions` / `dWeight_compose_survivors` at the PMF level. -/
theorem length_keepWith (l d : List Bool) (hlen : d.length = l.length) :
    (keepWith l d).length = d.count true := by
  induction l generalizing d with
  | nil =>
    simp only [List.length_nil] at hlen
    rw [List.length_eq_zero_iff.mp hlen]; simp
  | cons a l ih =>
    cases d with
    | nil => simp at hlen
    | cons b d =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      cases b with
      | false => simp only [keepWith_cons_false, List.count_cons]; rw [ih d hlen]; simp
      | true => simp only [keepWith_cons_true, List.length_cons, List.count_cons]; rw [ih d hlen]; simp

/-! ### Summed two-stage composition engine (`master`)

The central marginalization identity driving the kernel-composition law, proved by
structural induction on the input bit list. -/

lemma dWeight_ofFn (w : Bool → ENNReal) (k : ℕ) (m : Fin k → Bool) :
    dWeight w (List.ofFn m) = ∏ i : Fin k, w (m i) := by
  simp [dWeight, List.map_ofFn, List.prod_ofFn]

lemma ofFn_cons (k : ℕ) (b : Bool) (x : Fin k → Bool) :
    List.ofFn (Fin.cons b x : Fin (k+1) → Bool) = b :: List.ofFn x := by
  rw [List.ofFn_succ]; simp [Fin.cons_zero, Fin.cons_succ]

lemma sum_fin_cons {n : ℕ} (f : (Fin (n+1) → Bool) → ENNReal) :
    ∑ x : Fin (n+1) → Bool, f x
      = ∑ b : Bool, ∑ x : Fin n → Bool, f (Fin.cons b x) := by
  rw [← Fintype.sum_prod_type']
  apply Fintype.sum_equiv (Fin.consEquiv (fun _ => Bool)).symm
  intro x
  show f x = f (Fin.cons (x 0) (Fin.tail x))
  rw [Fin.cons_self_tail]

lemma dWeight_ofFn_cons (w : Bool → ENNReal) (k : ℕ) (b : Bool) (x : Fin k → Bool) :
    dWeight w (List.ofFn (Fin.cons b x : Fin (k+1) → Bool)) = w b * dWeight w (List.ofFn x) := by
  rw [ofFn_cons, dWeight_cons]

/-- INNER_g: the inner survivor-mask sum over a fixed surviving list `s`. -/
noncomputable def innerS (w₂ : Bool → ENNReal) (g : List Bool → ENNReal) (s : List Bool) : ENNReal :=
  ∑ m : Fin s.length → Bool, g (keepWith s (List.ofFn m)) * dWeight w₂ (List.ofFn m)

-- peeling: innerS over (b :: s) splits.
set_option maxHeartbeats 1000000 in
lemma innerS_cons (w₂ : Bool → ENNReal) (g : List Bool → ENNReal) (b : Bool) (s : List Bool) :
    innerS w₂ g (b :: s)
      = w₂ true * innerS w₂ (fun l => g (b :: l)) s
        + w₂ false * innerS w₂ g s := by
  unfold innerS
  have hlen : (b :: s).length = s.length + 1 := by simp
  rw [hlen]
  rw [sum_fin_cons]
  rw [Fintype.sum_bool]
  -- now: (m0=true term) + (m0=false term)
  congr 1
  · -- true branch
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro mr _
    rw [ofFn_cons]
    rw [keepWith_cons_true, dWeight_cons]
    ring
  · -- false branch
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro mr _
    rw [ofFn_cons]
    rw [keepWith_cons_false, dWeight_cons]
    ring

-- LHS expressed via innerS
set_option maxHeartbeats 1000000 in
lemma master (w₁ w₂ w : Bool → ENNReal)
    (hT : w₁ true * w₂ true = w true)
    (hF : w₁ false + w₁ true * w₂ false = w false)
    (bits : List Bool) :
    ∀ (g : List Bool → ENNReal),
    (∑ x : Fin bits.length → Bool,
        dWeight w₁ (List.ofFn x) * innerS w₂ g (keepWith bits (List.ofFn x)))
      = ∑ e : Fin bits.length → Bool,
          g (keepWith bits (List.ofFn e)) * dWeight w (List.ofFn e) := by
  induction bits with
  | nil =>
    intro g
    simp [innerS, dWeight]
  | cons b bits ih =>
    intro g
    have hlen : (b :: bits).length = bits.length + 1 := by simp
    rw [hlen]
    -- LHS: split outer over x0
    rw [sum_fin_cons, Fintype.sum_bool]
    -- RHS: split outer over e0
    conv_rhs => rw [sum_fin_cons, Fintype.sum_bool]
    -- Now simplify each branch.
    -- LHS true branch: dWeight w₁ (ofFn (cons true xr)) * innerS w₂ g (keepWith (b::bits) (ofFn (cons true xr)))
    have lhs_true :
        (∑ xr : Fin bits.length → Bool,
          dWeight w₁ (List.ofFn (Fin.cons true xr : Fin (bits.length+1) → Bool)) *
            innerS w₂ g (keepWith (b :: bits) (List.ofFn (Fin.cons true xr : Fin (bits.length+1) → Bool))))
          = ∑ xr : Fin bits.length → Bool,
              w₁ true * dWeight w₁ (List.ofFn xr) *
                (w₂ true * innerS w₂ (fun l => g (b :: l)) (keepWith bits (List.ofFn xr))
                  + w₂ false * innerS w₂ g (keepWith bits (List.ofFn xr))) := by
      apply Finset.sum_congr rfl
      intro xr _
      rw [dWeight_ofFn_cons, ofFn_cons, keepWith_cons_true, innerS_cons]
    have lhs_false :
        (∑ xr : Fin bits.length → Bool,
          dWeight w₁ (List.ofFn (Fin.cons false xr : Fin (bits.length+1) → Bool)) *
            innerS w₂ g (keepWith (b :: bits) (List.ofFn (Fin.cons false xr : Fin (bits.length+1) → Bool))))
          = ∑ xr : Fin bits.length → Bool,
              w₁ false * dWeight w₁ (List.ofFn xr) * innerS w₂ g (keepWith bits (List.ofFn xr)) := by
      apply Finset.sum_congr rfl
      intro xr _
      rw [dWeight_ofFn_cons, ofFn_cons, keepWith_cons_false]
    rw [lhs_true, lhs_false]
    -- RHS true/false branches
    have rhs_true :
        (∑ er : Fin bits.length → Bool,
          g (keepWith (b :: bits) (List.ofFn (Fin.cons true er : Fin (bits.length+1) → Bool))) *
            dWeight w (List.ofFn (Fin.cons true er : Fin (bits.length+1) → Bool)))
          = ∑ er : Fin bits.length → Bool,
              w true * (g (b :: keepWith bits (List.ofFn er)) * dWeight w (List.ofFn er)) := by
      apply Finset.sum_congr rfl
      intro er _
      rw [dWeight_ofFn_cons, ofFn_cons, keepWith_cons_true]
      ring
    have rhs_false :
        (∑ er : Fin bits.length → Bool,
          g (keepWith (b :: bits) (List.ofFn (Fin.cons false er : Fin (bits.length+1) → Bool))) *
            dWeight w (List.ofFn (Fin.cons false er : Fin (bits.length+1) → Bool)))
          = ∑ er : Fin bits.length → Bool,
              w false * (g (keepWith bits (List.ofFn er)) * dWeight w (List.ofFn er)) := by
      apply Finset.sum_congr rfl
      intro er _
      rw [dWeight_ofFn_cons, ofFn_cons, keepWith_cons_false]
      ring
    rw [rhs_true, rhs_false]
    -- Now regroup LHS: combine the two sums and split innerS coefficients.
    rw [← Finset.sum_add_distrib]
    have combine :
        (∑ xr : Fin bits.length → Bool,
          (w₁ true * dWeight w₁ (List.ofFn xr) *
            (w₂ true * innerS w₂ (fun l => g (b :: l)) (keepWith bits (List.ofFn xr))
              + w₂ false * innerS w₂ g (keepWith bits (List.ofFn xr)))
           + w₁ false * dWeight w₁ (List.ofFn xr) * innerS w₂ g (keepWith bits (List.ofFn xr))))
          = (w true) * (∑ xr : Fin bits.length → Bool,
                dWeight w₁ (List.ofFn xr) * innerS w₂ (fun l => g (b :: l)) (keepWith bits (List.ofFn xr)))
            + (w false) * (∑ xr : Fin bits.length → Bool,
                dWeight w₁ (List.ofFn xr) * innerS w₂ g (keepWith bits (List.ofFn xr))) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro xr _
      have e1 : w₁ true * dWeight w₁ (List.ofFn xr) * (w₂ true * innerS w₂ (fun l => g (b :: l)) (keepWith bits (List.ofFn xr)))
          = w true * (dWeight w₁ (List.ofFn xr) * innerS w₂ (fun l => g (b :: l)) (keepWith bits (List.ofFn xr))) := by
        rw [← hT]; ring
      have e2 : w₁ true * dWeight w₁ (List.ofFn xr) * (w₂ false * innerS w₂ g (keepWith bits (List.ofFn xr)))
            + w₁ false * dWeight w₁ (List.ofFn xr) * innerS w₂ g (keepWith bits (List.ofFn xr))
          = w false * (dWeight w₁ (List.ofFn xr) * innerS w₂ g (keepWith bits (List.ofFn xr))) := by
        rw [← hF]; ring
      calc _ = (w₁ true * dWeight w₁ (List.ofFn xr) * (w₂ true * innerS w₂ (fun l => g (b :: l)) (keepWith bits (List.ofFn xr))))
              + (w₁ true * dWeight w₁ (List.ofFn xr) * (w₂ false * innerS w₂ g (keepWith bits (List.ofFn xr)))
                 + w₁ false * dWeight w₁ (List.ofFn xr) * innerS w₂ g (keepWith bits (List.ofFn xr))) := by ring
        _ = _ := by rw [e1, e2]
    rw [combine]
    -- apply IH at g' and g
    rw [ih (fun l => g (b :: l)), ih g]
    -- RHS after rhs_true/rhs_false: ∑ er, w true * (...) and ∑ er, w false * (...)
    rw [← Finset.mul_sum, ← Finset.mul_sum]

end TraceDeletionListCompose
