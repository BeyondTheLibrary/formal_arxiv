import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm75Setup

/-!
# Rung replacement: the new appearance `L(H′)`

PAPER (proof of 7.5, claim (2), printed p. 37):

*"In case 1, let `R′` be the (unique) path from `p₁` to `s₂` in `(V(P) ∪ V(Rb₁b₂)) \ {s₁}`, and
in the other cases let `R′` be `P`.  So if in `L(H)` we replace `Rb₁b₂` by `R′` we obtain another
appearance of `J` in `G`, say `L(H′)`, where `H′` is obtained from `H` by replacing the branch
`Bb₁b₂` by some new branch `B′` joining the same two vertices.  For each `v ∈ V(J)` let `N′v` be
the clique in `L(H′)` formed by the edges in `δ_H′(v)`.  So `N′v = Nv` for all vertices `v` of
`J` except for `b₁` and `b₂`.  Let `R′` be between `r′₁` and `r′₂`, where `r′ᵢ ∈ N′_{bᵢ}`."*

This module is that construction, and nothing else: given an appearance `L(H)`, a branch
`q = Bb₁b₂` of `H` whose rung is the path `R` of `G`, and a replacement path `R′` of `G` that is
disjoint from `K = V(L(H))`, attaches to `K` only at the two clique-remainders
`N_{b₁} \ {r₁}` and `N_{b₂} \ {r₂}`, and has the same parity as `R`, there is a new appearance
`L(H′)` of the same `J` whose vertex set is `K` with `V(R)` swapped out for `V(R′)`, in which
`Bb₁b₂` has been replaced by a new branch with the same ends, the two cliques `N_{bᵢ}` have had
`rᵢ` swapped for `r′ᵢ`, every other clique is unchanged, and every branch of `H` other than
`Bb₁b₂` survives.

`ι : W → Fin m` is the (injective on branch-vertices) relabelling of `H`'s vertices inside
`H′`; it is what lets the caller say *"`Bc₁c₂` is still a branch of `H′`"* for the branch
`c₁c₂ ≠ b₁b₂`, and *"`N′v = Nv` for all vertices `v` of `J` except for `b₁` and `b₂`"*.
Targeting `Fin m` rather than an abstract second vertex type is deliberate: with
`Workspace.ProofLemmas.AppearanceVertexTypeTransport` available it costs the caller nothing, and
it keeps the induction of claim (2) inside `Type 0`.

## THE PARITY GAP — read this before proving or before citing

`hpar` (*"`R′` has the same parity as `R`"*) is **load-bearing and is not free**.  `IsAppearance`
requires `H′` to be a *bipartite* subdivision of `J`; replacing a single track of a subdivision
shifts the length of every cycle of `H′` through that track by
`trackLength B′ − trackLength Bb₁b₂`, so `H′` is bipartite iff that difference is even, i.e. iff
`R′` and `R` have the same parity.  Without `hpar` the conclusion is simply false.

The printed proof supplies `hpar` in only **three** of the four 5.8.2 cases:

* case 2 — states it outright: *"and `P` has the same parity as `Rb₁b₂`"*, and there `R′ = P`;
* case 3 — states *"and `Rb₁b₂` is even"*, and there `p₁ = p₂`, so `R′ = P = [p₁]` has length `0`,
  which is even;
* case 4 — states *"and `P` is even"* together with `s₁ = s₂`, so `Rb₁b₂` is a single vertex,
  `R` has length `0`, and `R′ = P` is even.

In **case 1** — *"let `R′` be the (unique) path from `p₁` to `s₂` in
`(V(P) ∪ V(Rb₁b₂)) \ {s₁}`"* — no parity statement is printed, and none is derivable from the
hypotheses that 5.8.1 case 1 supplies (`P` may have either parity, and `R′` is a splice of `P`
with an arbitrary terminal segment of `Rb₁b₂`).  Yet the paper still concludes, uniformly over
all four cases, *"we obtain another appearance of `J` in `G`"*.

**Open question for the caller.**  Either case 1 needs a parity argument the authors omitted, or
case 1 has to be excluded on other grounds before the replacement is performed.  Note that in
the `bᵢ = cᵢ` branch of the argument the paper *does* dispose of case 1 separately (*"case 1 is
impossible, by applying 7.4 as before …"*), so the gap is live only in the `b₁b₂ ≠ c₁c₂` branch.
Whoever proves claim (2) must confront this: do **not** silently instantiate this module in case
1 without discharging `hpar`.

## Provenance

The paper prints **no** proof of this construction (p. 37: *"So if in `L(H)` we replace `Rb₁b₂`
by `R′` we obtain another appearance of `J` in `G`"*, asserted and not argued).  By
`PROVER_TASK.md` §1, *"any correct proof is acceptable"* here.

**Status: statement only — this module is a work item.**
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm75AppearanceFromRungReplacement

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm75Setup

/-- **Replacing the rung `Rb₁b₂` by `R′` produces a new appearance `L(H′)` of `J`.**

`q` is the branch `Bb₁b₂` of `H`, `R` its rung in `G` (`hRset`), `rᵢ` the unique vertex of `R`
in `N_{bᵢ}`, and `R′` the replacement path with ends `r′₁, r′₂`, disjoint from `K` and attaching
to `K` only through `N_{b₁} \ {r₁}` (at `r′₁`) and `N_{b₂} \ {r₂}` (at `r′₂`).

`hpar` is the parity hypothesis discussed at length in the module docstring: it is what keeps
`H′` bipartite, and the paper does not supply it in 5.8.2's case 1. -/
theorem appearanceFromRungReplacement {V U W : Type*} [Fintype V] [DecidableEq V]
    [Fintype U] [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (H : SimpleGraph W) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G J H K)
    (q : List W) (b₁ b₂ : W) (hq : IsBranch H q) (hqf : IsTrackFrom H q b₁ b₂)
    (R : List V) (hR : IsPathList G R)
    (hRset : {x : V | x ∈ R} = {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
        e ∈ trackEdges q ∧ x = (↑(φ ⟨e, he⟩) : V)})
    (r₁ r₂ : V) (hr₁ : NSet G H K φ b₁ ∩ {x : V | x ∈ R} = {r₁})
                (hr₂ : NSet G H K φ b₂ ∩ {x : V | x ∈ R} = {r₂})
    (R' : List V) (r₁' r₂' : V) (hR' : IsPathFrom G R' r₁' r₂') (hR'K : ∀ x ∈ R', x ∉ K)
    (h₁ : ∀ x ∈ NSet G H K φ b₁ \ {r₁}, G.Adj r₁' x)
    (h₂ : ∀ x ∈ NSet G H K φ b₂ \ {r₂}, G.Adj r₂' x)
    (hno : ∀ x ∈ R', ∀ y ∈ K, G.Adj x y →
        (x = r₁' ∧ y ∈ NSet G H K φ b₁ \ {r₁}) ∨ (x = r₂' ∧ y ∈ NSet G H K φ b₂ \ {r₂}))
    (hpar : Even (pathLength R') ↔ Even (pathLength R)) :
    ∃ (m : ℕ) (H' : SimpleGraph (Fin m)) (K' : Set V) (φ' : H'.lineGraph ≃g G.induce K')
      (ι : W → Fin m) (q' : List (Fin m)),
      IsAppearance G J H' K' ∧
      K' = (K \ {x : V | x ∈ R}) ∪ {x : V | x ∈ R'} ∧
      IsBranch H' q' ∧ IsTrackFrom H' q' (ι b₁) (ι b₂) ∧
      NSet G H' K' φ' (ι b₁) = (NSet G H K φ b₁ \ {r₁}) ∪ {r₁'} ∧
      NSet G H' K' φ' (ι b₂) = (NSet G H K φ b₂ \ {r₂}) ∪ {r₂'} ∧
      (∀ c : W, c ≠ b₁ → c ≠ b₂ → NSet G H' K' φ' (ι c) = NSet G H K φ c) ∧
      (∀ p : List W, IsBranch H p → trackEdges p ≠ trackEdges q → IsBranch H' (p.map ι)) := by
  sorry

end Workspace.ProofLemmas.Thm75AppearanceFromRungReplacement
