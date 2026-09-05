import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm61Setup

/-!
# The three named claims of the even case of 6.1, as predicates

PAPER (proof of 6.1, printed pp. 31–32).  After *"In view of (7) we may henceforth assume that
`Q` is even"* the printed proof establishes three general-purpose claims, and then runs a long
configuration argument ((11), (12), (13) and the closing paragraph) that uses them repeatedly:

> *"(8) Every edge in `X₁` meets every edge in `X₂`."*
>
> *"A vertex of a track `P` is penultimate if it is adjacent in `P` to an end of `P`.*
>
> *(9) For all `W ∈ {X, X ∪ X₁, X ∪ X₂}` and for every even track `P` in `H` of length `≥ 4`
> and with both end-edges and no internal edges in `W`, every edge in `W` is incident with a
> penultimate vertex of `P`."*
>
> *"(10) If `P₁, P₂, P₃` are tracks in `H` with a common end `v`, say, and otherwise
> vertex-disjoint, each with an edge in `X`, then at least two of the three edges of
> `P₁ ∪ P₂ ∪ P₃` incident with `v` belong to `X`."*

This module only *names* the three claims, so that the module proving a claim and the module
consuming it agree on its statement byte-for-byte.  Nothing is proved here.

Encoding notes.

* `X = completeEdges G H K φ Y` and `Xᵢ = extraEdges G H K φ Y yᵢ`
  (`Workspace.ProofLemmas.Thm61Setup`).  By `Thm61Setup.X_Xi_facts`,
  `X ∪ Xᵢ = completeEdges G H K φ (Y \ {yᵢ})`, so the paper's
  `W ∈ {X, X ∪ X₁, X ∪ X₂}` is rendered as `W = completeEdges G H K φ Y'` with
  `Y' ∈ {Y, Y \ {y₁}, Y \ {y₂}}` — which is exactly the reformulation the printed proof of (9)
  opens with (*"If `W = X` let `Y' = Y`, and if `W = X ∪ Xᵢ` … let `Y' = Y \ {yᵢ}`.  So `W` is
  the set of `Y'`-complete vertices of `L(H)`"*).
* A track is a list `P` of vertices; its edges are the consecutive pairs.  *"length `≥ 4`"* is
  `5 ≤ P.length`; *"both end-edges … in `W`"* is `s(P[0],P[1]), s(P[len-2],P[len-1]) ∈ W`; *"no
  internal edges in `W`"* is the clause on the edges `s(P[i],P[i+1])` for `1 ≤ i` and
  `i + 2 < P.length`.  The *penultimate* vertices of `P` are `P[1]` and `P[len-2]`.
* In (10), *"the three edges of `P₁ ∪ P₂ ∪ P₃` incident with `v`"* are the first edges
  `s(Pᵢ[0], Pᵢ[1])` of the three tracks (each `Pᵢ` starts at the common end `v`), and *"at
  least two of them belong to `X`"* is the three-way disjunction of pairs.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm61EvenClaims

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup

/-- **6.1(8)** *"Every edge in `X₁` meets every edge in `X₂`."* -/
def Claim8 {V : Type*} (G : SimpleGraph V) {n : ℕ} (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (Y : Set V) (y₁ y₂ : V) : Prop :=
  ∀ h₁ h₂ : Sym2 (Fin n),
    h₁ ∈ extraEdges G H K φ Y y₁ → h₂ ∈ extraEdges G H K φ Y y₂ → MeetEdges h₁ h₂

/-- **6.1(9)** *"For all `W ∈ {X, X ∪ X₁, X ∪ X₂}` and for every even track `P` in `H` of
length `≥ 4` and with both end-edges and no internal edges in `W`, every edge in `W` is
incident with a penultimate vertex of `P`."* -/
def Claim9 {V : Type*} (G : SimpleGraph V) {n : ℕ} (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (Y : Set V) (y₁ y₂ : V) : Prop :=
  ∀ Y' : Set V, (Y' = Y ∨ Y' = Y \ {y₁} ∨ Y' = Y \ {y₂}) →
    ∀ P : List (Fin n), IsTrackList H P → ∀ _hlen : 5 ≤ P.length, Even (trackLength P) →
      s(P[0]'(by omega), P[1]'(by omega)) ∈ completeEdges G H K φ Y' →
      s(P[P.length - 2]'(by omega), P[P.length - 1]'(by omega))
        ∈ completeEdges G H K φ Y' →
      (∀ i : ℕ, 1 ≤ i → ∀ _hi : i + 2 < P.length,
        s(P[i]'(by omega), P[i + 1]'(by omega)) ∉ completeEdges G H K φ Y') →
      ∀ f ∈ completeEdges G H K φ Y',
        (P[1]'(by omega)) ∈ f ∨ (P[P.length - 2]'(by omega)) ∈ f

/-- **6.1(10)** *"If `P₁, P₂, P₃` are tracks in `H` with a common end `v`, say, and otherwise
vertex-disjoint, each with an edge in `X`, then at least two of the three edges of
`P₁ ∪ P₂ ∪ P₃` incident with `v` belong to `X`."* -/
def Claim10 {V : Type*} (G : SimpleGraph V) {n : ℕ} (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (Y : Set V) : Prop :=
  ∀ (v v₁ v₂ v₃ : Fin n) (P₁ P₂ P₃ : List (Fin n)),
    IsTrackFrom H P₁ v v₁ → IsTrackFrom H P₂ v v₂ → IsTrackFrom H P₃ v v₃ →
    ∀ _h₁ : 2 ≤ P₁.length, ∀ _h₂ : 2 ≤ P₂.length, ∀ _h₃ : 2 ≤ P₃.length,
      (∀ w ∈ P₁, w ∈ P₂ → w = v) → (∀ w ∈ P₁, w ∈ P₃ → w = v) →
      (∀ w ∈ P₂, w ∈ P₃ → w = v) →
      (∃ e ∈ trackEdges P₁, e ∈ completeEdges G H K φ Y) →
      (∃ e ∈ trackEdges P₂, e ∈ completeEdges G H K φ Y) →
      (∃ e ∈ trackEdges P₃, e ∈ completeEdges G H K φ Y) →
      (s(P₁[0]'(by omega), P₁[1]'(by omega)) ∈ completeEdges G H K φ Y ∧
        s(P₂[0]'(by omega), P₂[1]'(by omega)) ∈ completeEdges G H K φ Y) ∨
      (s(P₁[0]'(by omega), P₁[1]'(by omega)) ∈ completeEdges G H K φ Y ∧
        s(P₃[0]'(by omega), P₃[1]'(by omega)) ∈ completeEdges G H K φ Y) ∨
      (s(P₂[0]'(by omega), P₂[1]'(by omega)) ∈ completeEdges G H K φ Y ∧
        s(P₃[0]'(by omega), P₃[1]'(by omega)) ∈ completeEdges G H K φ Y)

end Workspace.ProofLemmas.Thm61EvenClaims
