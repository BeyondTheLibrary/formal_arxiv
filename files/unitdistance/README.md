# Planar Point Sets with Many Unit Distances — a Lean 4 formalization

This repository contains a machine-checked Lean 4 proof of the paper's main theorem.

```lean
theorem theorem_1_1_unit_distance :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧
      (nuMax n : ℝ) ≥ (n : ℝ) ^ ((1 : ℝ) + δ)
```

where `nu P` is the number of unordered pairs of distinct points of a finite planar set `P` at
Euclidean distance exactly `1`, and `nuMax n` is its maximum over all `n`-point subsets of
`EuclideanSpace ℝ (Fin 2)` (see `Workspace/Types/PlanarCounting.lean`).  This is Theorem 1.1 of the
paper: there is an absolute `δ > 0` with `ν(n) ≥ n^{1+δ}` for infinitely many `n`.

## Verifying

Requires Lean `leanprover/lean4:v4.30.0-rc2` and the pinned Mathlib checkout.

```bash
cd lean_workspace
lake build Workspace           # full build: 8542 jobs, 0 errors, no `sorry`
lake env lean AxiomCheck.lean  # axiom audit (see below)
```

## What is admitted

The proof is complete except for **two** classical theorems, which the paper itself cites as prior
work (both are stated in `Workspace/PriorWork/`, each with its literature citation):

| axiom | paper label | statement |
|---|---|---|
| `GolodShafarevichFiltration` | Prop. 3.4 / A.9 | the augmentation-filtration input to the Golod–Shafarevich inequality (Golod–Shafarevich 1964) |
| `ShafarevichRelationRank` | Prop. 3.5 / A.10 | `r(G) ≤ d(G) + C₀` for `G = Gal(F^{ur,3}/F)`, `F` totally real cubic (Shafarevich 1963) |

`AxiomCheck.lean` prints the axiom dependencies of the main theorem and of **every** prior-work
statement the formalization relies on:

```
'Workspace.MainTheorem.theorem_1_1_unit_distance' depends on axioms:
  [GolodShafarevichFiltration, ShafarevichRelationRank, propext, Classical.choice, Quot.sound]
```

Every other prior-work statement the formalization relies on is now **proved from Mathlib** (audit
line `[propext, Classical.choice, Quot.sound]`) and lives in `Workspace/ProofLemmas/`.  Only the two
axioms above remain admitted, collected in `Workspace/PriorWork/`, and both are used by the main
theorem.

## Layout

```
lean_workspace/
  Workspace/Types/        formalized definitions (planar counting, ramification, pro-p groups, …)
  Workspace/ProofLemmas/  the proof, factored into named lemmas (including the former
                          prior-work statements now proved from Mathlib)
  Workspace/PriorWork/    the two axioms still admitted from the literature
  Workspace/MainTheorem.lean
  AxiomCheck.lean         axiom audit
  MainTheorem_flat.lean   single-file merge (see the caveat in ../proving_notes.md)
theorem_text.md           the natural-language extraction the formalization was checked against
proving_notes.md          what was proved, how, and what is left
```
