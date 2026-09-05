import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Tracks
import Workspace.Types.Classes
import Workspace.ProofLemmas.OddWheelArc
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.LineGraphK4ChordsCompletion

/-!
# A hole with two nonadjacent hubs is the line graph of a bipartite subdivision of `K₄`

PAPER (16.1, printed p. 97), the last sentence of the proof of claim (1):

> *"But then `G|(V(C) ∪ {v,y})` is the line graph of a bipartite subdivision of `K₄`,
> a contradiction."*

The configuration the printed proof has reached at that point is: a hole `C` with vertices
`p₁, …, pₙ` in order, and two nonadjacent vertices `v, y ∉ V(C)` such that

* `v` has exactly the four neighbours `p₁, p_j, p_{j+1}, pₙ` in `C`, and
* `y` has exactly the four neighbours `p_i, p_{i+1}, p_k, p_{k+1}` in `C`,

with `1 ≤ i < i+1 < j < j+1 ≤ k < k+1 ≤ n-1`, and with the parities the printed proof has
established: `n` even, `j` odd, `i` odd, `k` even.

In the indexing of `OddWheelArc` — `D t` is the rim vertex at cyclic position `k₀ + t`, so the
paper's `p_a` is `D (a-1)` — the paper's `j` is `L+1`, its `i` is `s+1` and its `k` is `c+1`;
the parities read `n % 2 = 0`, `L % 2 = 0`, `s % 2 = 0`, `c % 2 = 1`.

## Why this is the line graph of a bipartite subdivision of `K₄`

Let `H` be the graph whose vertices are the `n` *corners* of the cycle — corner `t` sitting
between the rim vertices `D (t-1)` and `D t` — so that the rim vertex `D t` is the edge
`{t, t+1}` of the `n`-cycle on the corners, and `L(n`-cycle`) = C`.  Then

* `v` is the chord `{0, L+1}` (it meets exactly the cycle edges `{n-1,0}, {0,1}, {L,L+1},
  {L+1,L+2}`, i.e. exactly `D (n-1), D 0, D L, D (L+1)`), and
* `y` is the chord `{s+1, c+1}` (it meets exactly `D s, D (s+1), D c, D (c+1)`),

and the two chords are disjoint, i.e. `v` and `y` are nonadjacent.  So `H` is the `n`-cycle
plus the two chords `{0, L+1}` and `{s+1, c+1}`; since `0 < s+1 < L+1 < c+1 < n` these two
chords *interleave*, so their four ends are the four branch-vertices of a subdivision of `K₄`:
the two chords are the two unsubdivided opposite edges, and the four arcs of the cycle between
consecutive branch-corners are the four subdivided edges.  Finally `H` is **bipartite**,
coloured by the parity of the corner index: the cycle is even because `n` is even, and each
chord joins corners of opposite parity because `L+1` is odd and `s+1` is odd while `c+1` is
even — which is exactly the parity information the printed proof has accumulated.

Since `G ∈ F₆ ⊆ F₃`, and `F₃` forbids every induced subgraph of `G` isomorphic to `L(H)` for
`H` a bipartite subdivision of `K₄`, the configuration is impossible.

## Status

**Statement-only for now**: the construction of `H`, the verification of
`IsBipartiteSubdivision (⊤ : SimpleGraph (Fin 4)) H` and the isomorphism
`G|(V(C) ∪ {v,y}) ≃g L(H)` are being written.

Nothing here corresponds to a numbered result of the paper; it is the routine verification the
printed sentence leaves implicit.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.CycleTwoChordsAppearance

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*}

/-- **PAPER (16.1, proof of claim (1), last sentence):** *"But then `G|(V(C) ∪ {v,y})` is the
line graph of a bipartite subdivision of `K₄`, a contradiction."*

`D t` is the rim vertex at cyclic position `k₀ + t` (the convention of `OddWheelArc`); the
paper's `p_a` is `D (a-1)`, its `j` is `L+1`, its `i` is `s+1` and its `k` is `c+1`. -/
theorem no_two_hub_rim [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hG : InF6 G)
    {C : List V} {D : ℕ → V} {v y : V} {k₀ n L s c : ℕ}
    (hC : IsHoleList G C) (hn : 0 < C.length) (hnn : C.length = n)
    (hD : ∀ t : ℕ, C[(k₀ + t) % C.length]? = some (D t))
    (hvC : v ∉ C) (hyC : y ∉ C) (hvy : ¬ G.Adj v y)
    (hn2 : n % 2 = 0) (hL2 : L % 2 = 0) (hs2 : s % 2 = 0) (hc2 : c % 2 = 1)
    (hsL : s + 1 < L) (hLc : L + 1 ≤ c) (hcn : c + 1 ≤ n - 2)
    (hv : ∀ t, t < n → (G.Adj v (D t) ↔ (t = 0 ∨ t = L ∨ t = L + 1 ∨ t = n - 1)))
    (hy : ∀ t, t < n → (G.Adj y (D t) ↔ (t = s ∨ t = s + 1 ∨ t = c ∨ t = c + 1))) :
    False := by
  let E := C.rotate k₀
  obtain ⟨hE, hEn, hEget⟩ :=
    Workspace.ProofLemmas.OddWheelArc.rim_rot hC hn hD hnn
  have hEpos : 0 < E.length := by simp [E, hn]
  have hED : ∀ t : ℕ, E[t % E.length]? = some (D t) := by
    intro t
    have ht : t % E.length < E.length := Nat.mod_lt _ hEpos
    rw [List.getElem?_eq_getElem ht, hEget (t % E.length) ht]
    congr 1
    apply Workspace.ProofLemmas.OddWheelArc.rim_congr hC hD
    simp [E]
  have hne : v ≠ y := by
    intro heq
    have hLn : L < n := by omega
    have hvL : G.Adj v (D L) := (hv L hLn).2 (Or.inr (Or.inl rfl))
    have hyL : ¬ G.Adj y (D L) := by
      rw [hy L hLn]
      omega
    rw [heq] at hvL
    exact hyL hvL
  have hneven : Even n := Nat.even_iff.mpr hn2
  have hPodd : ¬ Even (L + 1) := by
    rw [Nat.not_even_iff]
    omega
  have hRQodd : ¬ Even ((s + 1) + (n - (c + 1))) := by
    rw [Nat.not_even_iff]
    omega
  refine Workspace.ProofLemmas.LineGraphK4Chords.not_inF3_of_two_chord_config
    hG.1.1 hE (by simpa [E] using hEn) hneven hED
    (show 0 < s + 1 by omega) (show s + 1 < L + 1 by omega)
    (show L + 1 < c + 1 by omega) (show c + 1 < n by omega)
    hPodd hRQodd (by simpa [E] using hvC) (by simpa [E] using hyC) hne hvy ?_ ?_
  · intro t ht
    rw [hv t ht]
    omega
  · intro t ht
    rw [hy t ht]
    omega

end Workspace.ProofLemmas.CycleTwoChordsAppearance
