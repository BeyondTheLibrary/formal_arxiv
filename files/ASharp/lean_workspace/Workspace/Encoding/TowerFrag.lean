import Workspace.Encoding.Procedure

open BigOperators
open Classical

namespace Workspace.Encoding.TowerFrag

/-! # Section 3.2 — `t`-feasibility (Def 3.3), towers of fragments (Def 3.4),
and existence of a tower of fragments (Lemma 3.5).

**Source**: `@../arXiv-2412.03540v1.tex`, Section 3.2: Definition `def:feas`
(`t`-feasibility), the "Towers of minimum fragments" definition, and the lemma
"For any `H` and `W`, there exists a tower of fragments of `(W,H)`."

This file builds on `Workspace.Encoding.Procedure`, which supplies the iteration
`Hstep`/`Rstep` and the facts `Rstep_subset_Hstep`, `Hstep_antitone`,
`Rset_subset`, `geSet_subset`, etc.

## Indexing / `b` note (faithfulness).

The paper's Definition `def:feas` defines `(b,t)`-feasibility and then defines
`t`-feasibility as "`(b,t)`-feasible for some `b`, witnessed by some `H ∈ ℋ`".
The tuple `b = b(W',H)` is *determined* by the witness `(W',H)` — it is the tuple
of cutoff indices `bIdx` along the iteration. Since `t`-feasibility quantifies `b`
existentially and `b` is a deterministic function of `(W',H)`, the existential over
`b` is redundant: `t`-feasible ⇔ "there exist `W'`, `H ∈ ℋ` with `|W' i| = |Z i| - t i`,
`W' i ⊆ Z i`, and `R_i(W',H) ⊆ Z i` for all `i < s`" (the `R_i(W',H) = Rstep W' H λ i`
already use the `b(W',H)` implicitly via the procedure). We therefore do not carry a
separate `b` quantifier; this matches the paper's `t`-feasibility exactly.

Indexing is 0-based (as in `Procedure`): `Rstep W' H λ i` is the paper's
`R_{i+1}(W',H)`, and `Hstep W' H λ 0 = H`. All conditions are quantified over
indices `i < s`. -/

variable {X : Type} [Fintype X] [DecidableEq X]

/-! ## Definition 3.3 — `t`-feasibility. -/

/-- **Definition 3.3 (`def:feas`, `t`-feasibility).**

A tuple `Z : ℕ → Finset X` is `t`-feasible (for `t : ℕ → ℕ`) with respect to the
hypothesis family `ℋ : Set (Finset X)`, sample bound `s`, and the *family* of
weights `lambda_vec : (H : Finset X) → H ∈ ℋ → X → ℝ` (one `λ_H` per `H ∈ ℋ`),
iff there exist a witness family `W' : ℕ → Finset X` and `H ∈ ℋ` (with membership
witness `hH`) such that for all `i < s`:

* `W' i ⊆ Z i`,
* `(W' i).card = (Z i).card - t i`, and
* `Rstep W' H (lambda_vec H hH) i ⊆ Z i` (i.e. `R_i(W',H) ⊆ Z_i`), where the
  procedure for the witness `H` uses *its own* weight `λ_H = lambda_vec H hH`.

The cutoff tuple `b = b(W',H)` of the paper is implicit in `Rstep` (each
`Rstep W' H lambda i = (H_i)_{<b_i}` uses `b_i = bIdx (W' i) (Hstep W' H λ i) λ`),
so it is not quantified separately — see the file header. -/
def TFeasible (ℋ : Set (Finset X)) (s : ℕ)
    (lambda_vec : (H : Finset X) → H ∈ ℋ → X → ℝ)
    (Z : ℕ → Finset X) (t : ℕ → ℕ) : Prop :=
  ∃ (W' : ℕ → Finset X) (H : Finset X) (hH : H ∈ ℋ),
    (∀ i, i < s → W' i ⊆ Z i ∧ (W' i).card = (Z i).card - t i) ∧
    (∀ i, i < s → Workspace.Encoding.Procedure.Rstep W' H (lambda_vec H hH) i ⊆ Z i)

/-! ## Definition 3.4 — tower of fragments. -/

/-- **Definition 3.4 (towers of fragments).**

Given a sample family `W : ℕ → Finset X` and a hypothesis `H` (the paper takes
`H ∈ ℋ`; we expose this predicate without baking in `H ∈ ℋ` — the existence lemma
supplies `H ∈ ℋ`, and the `TFeasible` witness range over `ℋ` carries the membership
requirement where the paper needs it), a tuple `T : ℕ → Finset X` is a *tower of
fragments* of `(W,H)` iff:

* (feasibility) `Z := fun i => T i ∪ W i` is `t`-feasible for `t := fun i => (T i).card`,
* (containment) `∀ i < s, T i ⊆ H` (the paper's `⋃_i T_i ⊆ H`), and
* (disjointness) `∀ i < s, Disjoint (T i) (W i)` (needed for the surjection recovery `W_i = Z_i ∖ T_i`). -/
def IsTowerOfFragments (ℋ : Set (Finset X)) (s : ℕ)
    (lambda_vec : (H : Finset X) → H ∈ ℋ → X → ℝ)
    (W : ℕ → Finset X) (H : Finset X) (T : ℕ → Finset X) : Prop :=
  TFeasible ℋ s lambda_vec (fun i => T i ∪ W i) (fun i => (T i).card) ∧
    (∀ i, i < s → T i ⊆ H) ∧
    (∀ i, i < s → Disjoint (T i) (W i))

/-! ## Lemma 3.5 — a tower of fragments exists. -/

open Workspace.Encoding.Procedure

/-- **Lemma 3.5 (a tower of fragments exists).**

For any `W : ℕ → Finset X` and `H ∈ ℋ`, the tuple
`Tstar i = Rstep W H (lambda_vec H hH) i \ W i` (using `H`'s own weight `λ_H`) is a
tower of fragments of `(W,H)`.

This is the paper's "simple observation that `T` with `T_i = R_i(W,H) ∖ W_i` is a
tower of fragments of `(W,H)`". -/
theorem exists_tower_of_fragments
    {ℋ : Set (Finset X)} {s : ℕ}
    {lambda_vec : (H : Finset X) → H ∈ ℋ → X → ℝ}
    (W : ℕ → Finset X) (H : Finset X) (hH : H ∈ ℋ) :
    IsTowerOfFragments ℋ s lambda_vec W H
      (fun i => Rstep W H (lambda_vec H hH) i \ W i) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (i) `t`-feasibility of `Z i = (R_i ∖ W_i) ∪ W_i` with `t_i = |R_i ∖ W_i|`,
    -- witnessed by `W' := W` and `H := H` (using `lambda_vec H hH`).
    refine ⟨W, H, hH, ?_, ?_⟩
    · intro i _hi
      constructor
      · -- `W i ⊆ (R_i ∖ W_i) ∪ W_i`
        exact Finset.subset_union_right
      · -- `(W i).card = |(R_i ∖ W_i) ∪ W_i| - |R_i ∖ W_i|`.
        -- `R_i ∖ W_i` and `W_i` are disjoint, so the union's card is the sum.
        set Ti : Finset X := Rstep W H (lambda_vec H hH) i \ W i with hTi
        have hdisj : Disjoint Ti (W i) := by
          rw [hTi]; exact Finset.sdiff_disjoint
        have hcard : (Ti ∪ W i).card = Ti.card + (W i).card :=
          Finset.card_union_of_disjoint hdisj
        -- goal: (W i).card = (Ti ∪ W i).card - |R_i ∖ W_i|; fold to Ti.card.
        show (W i).card = (Ti ∪ W i).card - Ti.card
        rw [hcard]
        omega
    · intro i _hi
      -- `Rstep W H (lambda_vec H hH) i ⊆ (R_i ∖ W_i) ∪ W_i`: set identity `A ⊆ (A \ B) ∪ B`.
      intro x hx
      by_cases hxW : x ∈ W i
      · exact Finset.mem_union_right _ hxW
      · refine Finset.mem_union_left _ ?_
        rw [Finset.mem_sdiff]
        exact ⟨hx, hxW⟩
  · -- (ii) `T_i ⊆ H` for `i < s`.
    intro i _hi
    -- `T_i = R_i ∖ W_i ⊆ R_i ⊆ H_i ⊆ H_0 = H`.
    have h1 : Rstep W H (lambda_vec H hH) i \ W i ⊆ Rstep W H (lambda_vec H hH) i :=
      Finset.sdiff_subset
    have h2 : Rstep W H (lambda_vec H hH) i ⊆ Hstep W H (lambda_vec H hH) i :=
      Rstep_subset_Hstep W H (lambda_vec H hH) i
    have h3 : Hstep W H (lambda_vec H hH) i ⊆ Hstep W H (lambda_vec H hH) 0 :=
      Hstep_antitone W H (lambda_vec H hH) (Nat.zero_le i)
    have h4 : Hstep W H (lambda_vec H hH) 0 = H := rfl
    calc Rstep W H (lambda_vec H hH) i \ W i
        ⊆ Rstep W H (lambda_vec H hH) i := h1
      _ ⊆ Hstep W H (lambda_vec H hH) i := h2
      _ ⊆ Hstep W H (lambda_vec H hH) 0 := h3
      _ = H := h4
  · -- (iii) `Disjoint (T_i) (W i)` for `i < s`.
    -- `T_i = R_i ∖ W_i` is disjoint from `W_i` by `Finset.sdiff_disjoint`.
    intro i _hi
    exact Finset.sdiff_disjoint

end Workspace.Encoding.TowerFrag
