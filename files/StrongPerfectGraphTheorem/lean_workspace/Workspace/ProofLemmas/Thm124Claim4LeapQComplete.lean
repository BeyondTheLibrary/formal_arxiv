/-  **12.4, printed claim (4) — the adjudication of the clause *"both `Q`-complete"*.**

    PAPER (printed p. 75), the sentence that this module is about:

    *"By 2.1 applied in `Ḡ`, there is a leap; that is, there exist adjacent `a, b ∈ R₀*`,
    **both `Q`-complete**, such that `b-u-Q-v-a` is an antipath."*

    ## The adjudication (already made; recorded here verbatim, not re-litigated)

    The printed *"both `Q`-complete"* does NOT follow from what is in scope, and it is also NOT
    NEEDED.  `IsLeapForPath Gᶜ p b a` constrains `{a, b}` only against the vertices of `p`
    itself, i.e. against `{b₁, u, q₁, …, q_k, v, a₁}`; it says nothing about a vertex of
    `Q \ {q₁,…,q_k}`, and `Q` is in general strictly larger than `{q₁,…,q_k}`.  Maximality of
    `Q` cannot supply the missing adjacency either: maximality quantifies over supersets
    `Q' ⊇ Q`, whereas `a, b ∈ R₀* ⊆ V(K)` and `Q ⊆ V(G) \ V(K)`, so `a` and `b` can never be
    candidates for enlarging `Q` — maximality is structurally incapable of constraining them.

    What the remainder of (4) actually consumes is strictly weaker and IS delivered by the
    leap: `a` and `b` are `G`-complete to the INTERIOR of the chosen antipath `q` (the vertices
    `q₁,…,q_k`, which do lie in `Q`).  That is exactly the "no other edges" half of
    `IsLeapForPath`.  So the printed clause is an unused embellishment — most plausibly the
    authors' shorthand for "complete to the `Q`-segment `q₁-⋯-q_k`" appearing in the notation
    "`b-u-Q-v-a`".

    ## Contents

    * `leap_vertex_not_mem_Q` — the obstruction, as a real Lean fact: a vertex of `R₀*` is
      never in `Q`.  This is the structural reason maximality of `Q` cannot deliver the printed
      `Q`-completeness.
    * `leap_adjacency_package` — the adjacency package the rest of (4) actually consumes,
      extracted from the leap alone.
    * `PrintedQCompleteClaim` / `printed_claim_implies_package` — the printed clause, isolated
      and labelled, together with the check that our replacement really is *weaker* than it
      (so nothing has been smuggled in).

    ## Provenance of every hypothesis of `leap_adjacency_package`

    No hypothesis has been strengthened to make anything compile.  Each is licensed by a
    printed sentence of claim (4):

    * `hu`, `hv` — *"suppose `uv` is such an edge"*, where the edge `uv` of (4) has *"`u` is a
      left-star, `v` is a right-star"*.
    * `hq`, `hqQ`, `hqlen` — *"Since `u`, `v` have nonneighbours in `Q` and `Q` is
      anticonnected, there is an antipath `u-q₁-⋯-q_k-v` with `q₁, …, q_k ∈ Q`"* (the length
      bound is the parity/`k`-even bookkeeping already banked in
      `Workspace.ProofLemmas.Thm124Claim4Leap.odd_antipath_for_leap_explicit`).
    * `ha`, `hb`, `hleap` — *"By 2.1 applied in `Ḡ`, there is a leap; that is, there exist
      adjacent `a, b ∈ R₀*` … such that `b-u-Q-v-a` is an antipath"*, i.e. exactly the output
      of `Workspace.ProofLemmas.Thm124Claim4Leap.leap_exists`.

    In particular the conclusion is derived from the leap ALONE: `VertexComplete G a Q` is
    never assumed anywhere outside `PrintedQCompleteClaim`.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.Thm124Setup
import Workspace.ProofLemmas.Thm124Claim4Part1
import Workspace.ProofLemmas.Thm124Claim4Leap

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace ProofAttempts.Thm124Claim4LeapQComplete

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Elementary plumbing -/

/-- Indexing a list at provably-equal indices gives the same element. -/
private theorem getElem_idx_eq {W : Type*} {l : List W} {i j : ℕ} (hij : i = j)
    (hi : i < l.length) (hj : j < l.length) : l[i]'hi = l[j]'hj := by
  subst hij; rfl

private theorem length_cons_append {W : Type*} (b₁ a₁ : W) (q : List W) :
    (b₁ :: (q ++ [a₁])).length = q.length + 2 := by
  simp

private theorem getElem_succ_cons_append {W : Type*} (b₁ a₁ : W) (q : List W) {i : ℕ}
    (hi : i < q.length) (h : i + 1 < (b₁ :: (q ++ [a₁])).length) :
    (b₁ :: (q ++ [a₁]))[i + 1]'h = q[i]'hi := by
  rw [List.getElem_cons_succ, List.getElem_append_left hi]

/-- `¬ Gᶜ.Adj x y` together with `x ≠ y` is `G.Adj x y`. -/
private theorem adj_of_not_compl_adj {G : SimpleGraph V} {x y : V} (hne : x ≠ y)
    (hc : ¬ Gᶜ.Adj x y) : G.Adj x y := by
  by_contra hcon
  exact hc ((SimpleGraph.compl_adj G x y).mpr ⟨hne, hcon⟩)

/-! ## D1 — the obstruction -/

/-- The structural reason maximality of `Q` cannot deliver the printed `Q`-completeness of the
leap vertices: the leap vertices live in `R₀* ⊆ V(K)`, and `Q` is disjoint from `V(K)`, so no
enlargement `Q' ⊇ Q` of `Q` ever mentions them.  Concretely, `Setup.outsideQ` says every
`q ∈ Q` avoids `staircaseVertices A C B R₀`, whose first component is `{v | v ∈ R₀}`, and an
interior vertex of `R₀` is in particular a member of `R₀`.

Hence *"there exist adjacent `a, b ∈ R₀*`, both `Q`-complete"* cannot be obtained by the usual
maximality argument, and (see the module doc-comment) it is not obtainable from
`IsLeapForPath` either.  It is also not needed. -/
theorem leap_vertex_not_mem_Q {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    {Q : Set V} (h : Thm124Setup.Setup G A C B a₀ R₀ b₀ Q) {a : V}
    (ha : a ∈ SPGT.interior R₀) : a ∉ Q :=
  h.notMemQ_of_mem a (PathBasics.interior_subset ha)

/-! ## D2 — the adjacency package the rest of (4) actually consumes -/

/-- PAPER: *"… there is a leap; that is, there exist adjacent `a, b ∈ R₀*`, both `Q`-complete,
such that `b-u-Q-v-a` is an antipath."*

This is everything the remainder of claim (4) uses about `a` and `b`, derived from the leap
`IsLeapForPath Gᶜ (b₁ :: (q ++ [a₁])) b a` **alone** — no `Q`-completeness is assumed.  Reading
`p = b₁-u-q₁-⋯-q_k-v-a₁`, the leap says `b` is `Ḡ`-adjacent exactly to `p₁ = b₁`, `p₂ = u`,
`pₙ = a₁` and `a` exactly to `p₁ = b₁`, `pₙ₋₁ = v`, `pₙ = a₁`.  Translated into `G`:

* `a` is `G`-nonadjacent to `v` and `b` is `G`-adjacent to `v`;
* `b` is `G`-nonadjacent to `u` and `a` is `G`-adjacent to `u`;
* both `a` and `b` are `G`-adjacent to every `q₁, …, q_k` — this is the *"`Q`-complete"* that
  the remainder of (4) actually consumes, namely completeness to the `Q`-segment of the
  antipath, and it is exactly the "no other edges" half of `IsLeapForPath`.

The distinctness conjuncts come from the surrounding configuration, not from the leap: `u` is
complete to the nonempty `A` and `v` to the nonempty `B`, while `R₀*` is anticomplete to
`A ∪ B ∪ C`, so `a, b ∉ {u, v}`; and every interior vertex of `q` lies in `Q`, which by
`leap_vertex_not_mem_Q` misses `a` and `b`. -/
theorem leap_adjacency_package {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    {Q : Set V} (h : Thm124Setup.Setup G A C B a₀ R₀ b₀ Q) {u v a₁ b₁ a b : V} {q : List V}
    (hu : IsLeftStar G A C B u) (hv : IsRightStar G A C B v)
    (hq : IsAntipathFrom G q u v) (hqlen : 3 ≤ pathLength q)
    (hqQ : ∀ z ∈ SPGT.interior q, z ∈ Q)
    (ha : a ∈ SPGT.interior R₀) (hb : b ∈ SPGT.interior R₀)
    (hleap : IsLeapForPath Gᶜ (b₁ :: (q ++ [a₁])) b a) :
    (¬ G.Adj a v) ∧ G.Adj b v ∧ (¬ G.Adj b u) ∧ G.Adj a u ∧
      (∀ w ∈ SPGT.interior q, G.Adj a w ∧ G.Adj b w) ∧
      a ≠ u ∧ a ≠ v ∧ b ≠ u ∧ b ≠ v ∧ (∀ w ∈ q, a ≠ w ∧ b ≠ w) := by
  classical
  -- `pathLength q = q.length - 1 ≥ 3`, so `q` has at least four vertices and `p` at least six
  have hpl : pathLength q = q.length - 1 := PathBasics.pathLength_eq q
  have hq4 : 4 ≤ q.length := by omega
  have hn : (b₁ :: (q ++ [a₁])).length = q.length + 2 := length_cons_append b₁ a₁ q
  obtain ⟨hppath, hp2, hbanea, hnadjba, hbadj, haadj⟩ := hleap
  -- ### index table for `p = b₁-u-q₁-⋯-q_k-v-a₁`
  have h1lt : (1 : ℕ) < (b₁ :: (q ++ [a₁])).length := by omega
  have hmlt : q.length < (b₁ :: (q ++ [a₁])).length := by omega
  have hqu : q[0]'(by omega) = u := PathBasics.getElem_zero_of_head? hq.2.1 (by omega)
  have hqv : q[q.length - 1]'(by omega) = v :=
    PathBasics.getElem_last_of_getLast? hq.2.2 (by omega)
  have hp1 : (b₁ :: (q ++ [a₁]))[1]'h1lt = u := by
    rw [getElem_idx_eq (show (1 : ℕ) = 0 + 1 by omega) h1lt (by omega),
      getElem_succ_cons_append b₁ a₁ q (show 0 < q.length by omega)]
    exact hqu
  have hpv : (b₁ :: (q ++ [a₁]))[q.length]'hmlt = v := by
    rw [getElem_idx_eq (show q.length = (q.length - 1) + 1 by omega) hmlt (by omega),
      getElem_succ_cons_append b₁ a₁ q (show q.length - 1 < q.length by omega)]
    exact hqv
  -- ### `a`, `b` are distinct from `u` and from `v`
  obtain ⟨aA, haA⟩ := h.stepConnected.2.1.1
  obtain ⟨bB, hbB⟩ := h.stepConnected.2.1.2
  have hanu : a ≠ u := by
    intro he
    exact h.interiorAnti a ha aA (Or.inl (Or.inl haA)) (he ▸ hu.2.1 aA haA)
  have hbnu : b ≠ u := by
    intro he
    exact h.interiorAnti b hb aA (Or.inl (Or.inl haA)) (he ▸ hu.2.1 aA haA)
  have hanv : a ≠ v := by
    intro he
    exact h.interiorAnti a ha bB (Or.inl (Or.inr hbB)) (he ▸ hv.2.1 bB hbB)
  have hbnv : b ≠ v := by
    intro he
    exact h.interiorAnti b hb bB (Or.inl (Or.inr hbB)) (he ▸ hv.2.1 bB hbB)
  -- ### `a`, `b` are distinct from every interior vertex of `q` (which lies in `Q`)
  have haQ : a ∉ Q := leap_vertex_not_mem_Q h ha
  have hbQ : b ∉ Q := leap_vertex_not_mem_Q h hb
  have hanw : ∀ w ∈ SPGT.interior q, a ≠ w := fun w hw he => haQ (he ▸ hqQ w hw)
  have hbnw : ∀ w ∈ SPGT.interior q, b ≠ w := fun w hw he => hbQ (he ▸ hqQ w hw)
  -- ### the four distinguished-index readings of the leap
  -- `Ḡ`-adjacency of `b` to `p₂ = u` holds (index `1`)
  have hbu : Gᶜ.Adj b u := by
    have := (hbadj 1 h1lt).mpr (Or.inr (Or.inl rfl))
    rwa [hp1] at this
  -- `Ḡ`-adjacency of `a` to `pₙ₋₁ = v` holds (index `p.length - 2 = q.length`)
  have hav : Gᶜ.Adj a v := by
    have := (haadj q.length hmlt).mpr (Or.inr (Or.inl (by omega)))
    rwa [hpv] at this
  -- `Ḡ`-adjacency of `a` to `p₂ = u` fails
  have hnau : ¬ Gᶜ.Adj a u := by
    intro hcon
    rw [← hp1] at hcon
    rcases (haadj 1 h1lt).mp hcon with h' | h' | h' <;> omega
  -- `Ḡ`-adjacency of `b` to `pₙ₋₁ = v` fails
  have hnbv : ¬ Gᶜ.Adj b v := by
    intro hcon
    rw [← hpv] at hcon
    rcases (hbadj q.length hmlt).mp hcon with h' | h' | h' <;> omega
  -- ### completeness of `a`, `b` to the interior `q₁, …, q_k` of the antipath
  have hint : ∀ w ∈ SPGT.interior q, G.Adj a w ∧ G.Adj b w := by
    intro w hw
    obtain ⟨k, hk, hk1, hk2, hkw⟩ := PathBasics.exists_getElem_of_mem_interior hq.1 hw
    have hklt : k + 1 < (b₁ :: (q ++ [a₁])).length := by omega
    have hpw : (b₁ :: (q ++ [a₁]))[k + 1]'hklt = w := by
      rw [getElem_succ_cons_append b₁ a₁ q hk]
      exact hkw
    constructor
    · refine adj_of_not_compl_adj (hanw w hw) ?_
      intro hcon
      rw [← hpw] at hcon
      rcases (haadj (k + 1) hklt).mp hcon with h' | h' | h' <;> omega
    · refine adj_of_not_compl_adj (hbnw w hw) ?_
      intro hcon
      rw [← hpw] at hcon
      rcases (hbadj (k + 1) hklt).mp hcon with h' | h' | h' <;> omega
  -- ### `a`, `b` are distinct from every vertex of `q`
  have hqne : ∀ w ∈ q, a ≠ w ∧ b ≠ w := by
    intro w hw
    by_cases hwu : w = u
    · exact ⟨by rw [hwu]; exact hanu, by rw [hwu]; exact hbnu⟩
    by_cases hwv : w = v
    · exact ⟨by rw [hwv]; exact hanv, by rw [hwv]; exact hbnv⟩
    have hwint : w ∈ SPGT.interior q :=
      (PathBasics.mem_interior_iff_of_pathFrom hq).mpr ⟨hw, hwu, hwv⟩
    exact ⟨hanw w hwint, hbnw w hwint⟩
  exact ⟨((SimpleGraph.compl_adj G a v).mp hav).2,
    adj_of_not_compl_adj hbnv hnbv,
    ((SimpleGraph.compl_adj G b u).mp hbu).2,
    adj_of_not_compl_adj hanu hnau,
    hint, hanu, hanv, hbnu, hbnv, hqne⟩

/-! ## D3 — the printed clause, isolated and labelled -/

/-- PAPER: *"there exist adjacent `a, b ∈ R₀*`, **both `Q`-complete**, …"*.  See the module
doc-comment: this is the one clause of claim (4) that does not follow from what the printed
argument has in scope, and it is also never used.  It is recorded here, not assumed. -/
def PrintedQCompleteClaim (G : SimpleGraph V) (Q : Set V) (a b : V) : Prop :=
  VertexComplete G a Q ∧ VertexComplete G b Q

/-- Our replacement really is *weaker* than the printed clause: had the paper's
`Q`-completeness been available, the adjacency package delivered by
`leap_adjacency_package` would follow at once, since `q₁, …, q_k ∈ Q`.  So nothing is being
smuggled in by dropping the printed clause. -/
theorem printed_claim_implies_package {G : SimpleGraph V} {Q : Set V} {q : List V} {a b : V}
    (hqQ : ∀ z ∈ SPGT.interior q, z ∈ Q) (hprinted : PrintedQCompleteClaim G Q a b) :
    ∀ w ∈ SPGT.interior q, G.Adj a w ∧ G.Adj b w :=
  fun w hw => ⟨hprinted.1 w (hqQ w hw), hprinted.2 w (hqQ w hw)⟩

end ProofAttempts.Thm124Claim4LeapQComplete
