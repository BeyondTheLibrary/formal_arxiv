import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.Types.Knots
import Workspace.Types.BasicClasses
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.DoubleSplitSelfComplementary
import Workspace.ProofLemmas.L33SelfComplementary
import Workspace.ProofLemmas.NoK4EnlargementAppearance
import Workspace.ProofLemmas.MaximalStriationExists
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.Statements.S07.Thm_7_5
import Workspace.Statements.S09.Thm_9_4

/-!
# 9.6, assembled from its printed steps

The printed proof of **9.6** (`paper/proofs/9_6.md`, published page 55) is long, and its
skeleton is a cascade of *"we may assume"* reductions followed by three numbered claims and a
closing paragraph.  This module carries the parts of that skeleton which are provable outright,
and takes the rest as `def`-wrapped hypotheses, so that the node closes with a single `exact`
as the pieces land.  (Same pattern as `Workspace.ProofLemmas.Thm53Assembly` and
`Workspace.ProofLemmas.Thm106Assembly`.)

## What is proved here

* **`Concl`** — 9.6's four-way conclusion, bundled, so that it can be named in the pieces.
* **`concl_compl : Concl Gᶜ → Concl G`.**  The single highest-leverage fact in the whole
  proof: the printed argument says *"by taking complements"* four separate times, and this is
  what makes every one of them legitimate.  Each of the four disjuncts is complement-stable —
  `IsDoubleSplitGraph` by `DoubleSplitSelfComplementary.isDoubleSplitGraph_compl`,
  `AdmitsBalancedSkewPartition` by `ClassLemmas.admitsBalancedSkewPartition_compl`, and the
  last two are literally symmetric in `G, Gᶜ`.  Note that `AdmitsProper2Join` on its own is
  **not** complement-closed (`ClassLemmas` records a six-vertex countermodel); it is only the
  *disjunction* `AdmitsProper2Join G ∨ AdmitsProper2Join Gᶜ` that is, which is exactly why 9.6
  states its third alternative that way.
* **`k4EnlargementFree`** — the opening sentence, *"So there is no appearance in `G` of a
  `K₄`-enlargement, and similarly there is none in `Ḡ`"*, delivered in the **disjunctive** form
  `¬ ∃ J', IsJEnlargement K₄ J' ∧ (Appears G J' ∨ Appears Gᶜ J')` that `thm_9_4` and `thm_9_5`
  demand.  It is `NoK4EnlargementAppearance.no_k4_enlargement_appears` used twice, the `Gᶜ`
  instance being fed by `L33SelfComplementary.no_L33_induced_compl` (9.6's hypothesis
  `hnoL33` is stated for `G` only, but `L(K₃,₃)` is self-complementary, so it holds for `Gᶜ`
  automatically).

## What is left as a piece

* **`StriationFromAppearance`** — *"By hypothesis it is degenerate, and hence there is a
  striation in `G`."*  This sentence carries **no citation anywhere in the paper**; it is the
  passage from a degenerate `K₄`-appearance, through §9's knot picture, to a striation.  It is
  stated for an arbitrary `Gx : SimpleGraph V` so that 9.6 can invoke it at `G` and at `Gᶜ`.
  (`MaximalStriationExists.exists_maximalStriation` then upgrades the striation to a maximal
  one; it does **not** produce the starting striation.)
* **`EightVertices`** — *"and consequently `|V(G)| ≥ 8`"*.  An appearance of `K₄` is an
  induced `L(H)` for `H` a **bipartite** subdivision of `K₄`; since `K₄` is not bipartite, at
  least two of its six edges are subdivided, so `|E(H)| ≥ 8` and `|K| = |E(H)|`.
* **`MainFromStriation`** — the mathematical body: claims (1), (2), (3) and the closing
  paragraph, i.e. everything downstream of the maximal striation and of 9.4's `M`/`N`
  partition.  Also stated for an arbitrary `Gx`, since claim (2), the bridge after claim (1)
  and the closing paragraph each say *"by taking complements"*.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm96Assembly

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.Types.BasicClasses Workspace.Types.BasicClasses.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

variable {V : Type*}

/-! ### 9.6's conclusion, bundled -/

/-- **9.6's four-way conclusion.**

PAPER: *"Then either `G` is a double split graph, or `G` admits a balanced skew partition, or
one of `G, Ḡ` admits a proper 2-join, or there is no appearance of `K₄` in either `G` or
`Ḡ`."*

Byte-identical to the conclusion of `Workspace.Statements.S09.SPGT.thm_9_6`. -/
def Concl (G : SimpleGraph V) : Prop :=
  IsDoubleSplitGraph G ∨
  AdmitsBalancedSkewPartition G ∨
  (AdmitsProper2Join G ∨ AdmitsProper2Join Gᶜ) ∨
  (¬ Appears G (⊤ : SimpleGraph (Fin 4)) ∧ ¬ Appears Gᶜ (⊤ : SimpleGraph (Fin 4)))

/-- **The conclusion of 9.6 is complement-stable.**

This is what licenses every one of the printed proof's four *"by taking complements"* steps:
having established the theorem for `Gᶜ`, one has it for `G`.

The third disjunct is handled by symmetry of the disjunction rather than by any
complement-closure of `AdmitsProper2Join`, which is false (`ClassLemmas`, line 43). -/
theorem concl_compl {G : SimpleGraph V} (h : Concl Gᶜ) : Concl G := by
  have hcc : Gᶜᶜ = G := compl_compl G
  rcases h with hds | hbsp | h2j | hnoapp
  · -- a double split graph: `IsDoubleSplitGraph Gᶜ → IsDoubleSplitGraph Gᶜᶜ = G`
    exact Or.inl (hcc ▸ DoubleSplitSelfComplementary.isDoubleSplitGraph_compl hds)
  · exact Or.inr (Or.inl (ClassLemmas.admitsBalancedSkewPartition_compl.mp hbsp))
  · refine Or.inr (Or.inr (Or.inl ?_))
    rcases h2j with h | h
    · exact Or.inr h
    · exact Or.inl (hcc ▸ h)
  · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
    · exact hcc ▸ hnoapp.2
    · exact hnoapp.1

/-! ### The opening sentence -/

/-- **PAPER (9.6, printed p. 55), the opening sentence.**

> *"If there is an appearance in `G` of some `K₄`-enlargement, say `L(H₀)`, then by 5.3,
> either `H₀ = K₃,₃`, which is impossible by hypothesis, or there is a subgraph `H₀₀` of `H₀`
> which is a bipartite subdivision of `K₄`, such that `L(H₀₀)` is nondegenerate, and again
> this is impossible by hypothesis.  So there is no appearance in `G` of a `K₄`-enlargement,
> and similarly there is none in `Ḡ`."*

Delivered in the disjunctive shape that `thm_9_4` and `thm_9_5` take as their `hnoenl`.

The *"and similarly there is none in `Ḡ`"* needs 9.6's `hnoL33` at `Gᶜ`, which is **not** among
9.6's hypotheses; it comes free because `L(K₃,₃)` is self-complementary. -/
theorem k4EnlargementFree {G : SimpleGraph V}
    (hdegG : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K →
        DegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H)
    (hdegGc : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V),
      IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K →
        DegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H)
    (hnoL33 : ¬ ∃ K : Set V,
      Nonempty ((completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ≃g G.induce K)) :
    ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears G J' ∨ Appears Gᶜ J') := by
  have hG := NoK4EnlargementAppearance.no_k4_enlargement_appears G hdegG hnoL33
  have hGc := NoK4EnlargementAppearance.no_k4_enlargement_appears Gᶜ hdegGc
    (L33SelfComplementary.no_L33_induced_compl hnoL33)
  rintro ⟨m, J', henl, happ | happ⟩
  · exact hG ⟨m, J', henl, happ⟩
  · exact hGc ⟨m, J', henl, happ⟩

/-! ### The 7.5 reduction -/

/-- **PAPER (9.6, printed p. 55).**

> *"Moreover, by 7.5, we may assume that there is no overshadowed appearance of `K₄` in `G` or
> in `Ḡ`."*

The *"we may assume"* is discharged against the second alternative of 9.6's own conclusion: if
there were an overshadowed appearance, 7.5 offers either a `K₄`-enlargement with a
nondegenerate appearance — which contradicts the opening sentence `k4EnlargementFree` — or a
balanced skew partition, which *is* the theorem.  Applied at `Gᶜ` as well as at `G`. -/
theorem overshadowedFree [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hG : Berge G)
    (hnoenl : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears G J' ∨ Appears Gᶜ J'))
    (hbsp : ¬ AdmitsBalancedSkewPartition G) :
    ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V)
      (φ : H.lineGraph ≃g G.induce K'),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧
        IsOvershadowedAppearance G H K' φ := by
  rintro ⟨n, H, K', φ, happ, hover⟩
  rcases _root_.Workspace.Statements.S07.SPGT.thm_7_5 G hG (⊤ : SimpleGraph (Fin 4))
      SubdivisionCounting.k4_three_connected H K' φ happ hover with h | h
  · obtain ⟨m, J', henl, n', H', K'', happ', -⟩ := h
    exact hnoenl ⟨m, J', henl, Or.inl ⟨n', H', K'', happ'⟩⟩
  · exact hbsp h

/-! ### The pieces still to be built -/

/-- **PIECE (9.6, printed p. 55).**

> *"By hypothesis it is degenerate, and hence there is a striation in `G`."*

This sentence carries **no citation anywhere in the paper**.  It is the passage from a
degenerate `K₄`-appearance, via §9's knot picture (*"There is another way to view them, not as
line graphs but as sets of paths and antipaths"*, printed p. 47), to a striation.

Stated for an arbitrary `Gx : SimpleGraph V` so that 9.6 can invoke it at `G` and at `Gᶜ`. -/
def StriationFromAppearance (Gx : SimpleGraph V) : Prop :=
  (∀ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V),
      IsAppearance Gx (⊤ : SimpleGraph (Fin 4)) H K →
        DegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H) →
  Appears Gx (⊤ : SimpleGraph (Fin 4)) →
  ∃ (m n : ℕ) (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V),
    IsStriation Gx S T

/-- **PIECE (9.6, printed p. 55).**

> *"We may assume that there is an appearance of `K₄` in one of `G, Ḡ`, and consequently
> `|V(G)| ≥ 8`."*

An appearance of `K₄` is an induced `L(H)` for `H` a **bipartite** subdivision of `K₄`.  `K₄`
is not bipartite, so at least two of its six edges are subdivided; hence `|E(H)| ≥ 8`, and the
appearance's vertex set `K` has `|K| = |E(H)|`. -/
def EightVertices (Gx : SimpleGraph V) : Prop :=
  Appears Gx (⊤ : SimpleGraph (Fin 4)) → 8 ≤ Nat.card V

/-- **PIECE (9.6, printed pp. 54–55): the mathematical body.**

Claims (1), (2), (3) and the closing paragraph — everything downstream of the maximal striation
and of 9.4's `M`/`N` partition:

> *"(1) If there exists `f ∈ N` with a nonneighbour in `V(S₁) ∪ ⋯ ∪ V(S_m)` then the theorem
> holds. … (2) If `M, N` are both nonempty then the theorem holds. … (3) If `M, N` are both
> empty then the theorem holds. … From (2) and (3), and taking complements if necessary, we may
> assume that `N` is empty and `M` is nonempty. … Then `(M₁ ∪ V(S₁), V(G) \ (M₁ ∪ V(S₁)))` is a
> proper 2-join of `G`.  This proves 9.6."*

Stated for an arbitrary `Gx` because claim (2), the bridge after claim (1) and the closing
paragraph each say *"by taking complements"*; `concl_compl` above is what makes those legitimate.

The `M`/`N` interface is exactly what `thm_9_4` delivers, one vertex at a time: `M` is the set
of vertices off `V(L)` whose neighbour set in `V(L)` is local with respect to `L`, and `N` the
set of those whose neighbour set resolves `L`. -/
def MainFromStriation (Gx : SimpleGraph V) : Prop :=
  Berge Gx →
  (¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
    IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears Gx J' ∨ Appears Gxᶜ J')) →
  (¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V) (φ : H.lineGraph ≃g Gx.induce K'),
    IsAppearance Gx (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gx H K' φ) →
  (¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V) (φ : H.lineGraph ≃g Gxᶜ.induce K'),
    IsAppearance Gxᶜ (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gxᶜ H K' φ) →
  8 ≤ Nat.card V →
  ∀ (m n : ℕ) (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V),
    MaximalStriation Gx S T →
    ∀ M N : Set V,
      M ∪ N = (striationVertices S T)ᶜ →
      Disjoint M N →
      (∀ v ∈ M, LocalForStriation Gx S T (Gx.neighborSet v ∩ striationVertices S T)) →
      (∀ v ∈ N, ResolvesStriation Gx S T (Gx.neighborSet v ∩ striationVertices S T)) →
      Concl Gx

/-! ### The assembly -/

/-- The `M`/`N` partition of `V(G) \ V(L)` supplied by 9.4, packaged. -/
private theorem exists_MN [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (hnoenl : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears G J' ∨ Appears Gᶜ J'))
    (hnoover : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V)
      (φ : H.lineGraph ≃g G.induce K'),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance G H K' φ)
    (hnoovercompl : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V)
      (φ : H.lineGraph ≃g Gᶜ.induce K'),
      IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gᶜ H K' φ)
    (m n : ℕ) (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V)
    (hL : MaximalStriation G S T) :
    ∃ M N : Set V,
      M ∪ N = (striationVertices S T)ᶜ ∧
      Disjoint M N ∧
      (∀ v ∈ M, LocalForStriation G S T (G.neighborSet v ∩ striationVertices S T)) ∧
      (∀ v ∈ N, ResolvesStriation G S T (G.neighborSet v ∩ striationVertices S T)) := by
  classical
  refine ⟨{v | v ∉ striationVertices S T ∧
      LocalForStriation G S T (G.neighborSet v ∩ striationVertices S T)},
    {v | v ∉ striationVertices S T ∧
      ¬ LocalForStriation G S T (G.neighborSet v ∩ striationVertices S T)},
    ?_, ?_, ?_, ?_⟩
  · ext v
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_compl_iff]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      by_cases hloc : LocalForStriation G S T (G.neighborSet v ∩ striationVertices S T)
      · exact Or.inl ⟨h, hloc⟩
      · exact Or.inr ⟨h, hloc⟩
  · rw [Set.disjoint_left]
    rintro v ⟨-, hloc⟩ ⟨-, hnloc⟩
    exact hnloc hloc
  · rintro v ⟨-, hloc⟩
    exact hloc
  · rintro v ⟨hv, hnloc⟩
    rcases _root_.Workspace.Statements.S09.SPGT.thm_9_4 G hG hnoenl hnoover hnoovercompl
        m n S T hL v hv (G.neighborSet v ∩ striationVertices S T) rfl with h | h
    · exact absurd h hnloc
    · exact h

/-- **9.6, assembled from its printed steps.**

`Workspace.Statements.S09.SPGT.thm_9_6` is `thm_9_6_of_steps G hG hdegG hdegGc hnoL33 hstr h8
hmain` once the three pieces are available; `Concl G` unfolds to the frozen conclusion by
`rfl`. -/
theorem thm_9_6_of_steps [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (hdegG : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K →
        DegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H)
    (hdegGc : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V),
      IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K →
        DegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H)
    (hnoL33 : ¬ ∃ K : Set V,
      Nonempty ((completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ≃g G.induce K))
    (hstr : ∀ Gx : SimpleGraph V, StriationFromAppearance Gx)
    (h8 : ∀ Gx : SimpleGraph V, EightVertices Gx)
    (hmain : ∀ Gx : SimpleGraph V, MainFromStriation Gx) :
    Concl G := by
  classical
  by_contra hcon
  have hcc : Gᶜᶜ = G := compl_compl G
  -- the fourth alternative fails, so `K₄` appears in one of `G`, `Gᶜ`
  have hexapp : Appears G (⊤ : SimpleGraph (Fin 4)) ∨ Appears Gᶜ (⊤ : SimpleGraph (Fin 4)) := by
    by_contra h
    push Not at h
    exact hcon (Or.inr (Or.inr (Or.inr ⟨h.1, h.2⟩)))
  -- the second alternative fails
  have hbspG : ¬ AdmitsBalancedSkewPartition G := fun h => hcon (Or.inr (Or.inl h))
  have hbspGc : ¬ AdmitsBalancedSkewPartition Gᶜ := fun h =>
    hbspG (ClassLemmas.admitsBalancedSkewPartition_compl.mp h)
  -- the opening sentence, and the 7.5 reduction, on both sides
  have hnoenl := k4EnlargementFree hdegG hdegGc hnoL33
  have hGc : Berge Gᶜ := HoleBasics.berge_compl.mpr hG
  have hnoenlc : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears Gᶜ J' ∨ Appears Gᶜᶜ J') := by
    rw [hcc]
    rintro ⟨m, J', he, h⟩
    exact hnoenl ⟨m, J', he, h.symm⟩
  have hnoover := overshadowedFree hG hnoenl hbspG
  have hnoovercompl := overshadowedFree hGc hnoenlc hbspGc
  -- the same two facts, read at `Gᶜ`
  have hnooverc' : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V)
      (φ : H.lineGraph ≃g Gᶜᶜ.induce K'),
      IsAppearance Gᶜᶜ (⊤ : SimpleGraph (Fin 4)) H K' ∧
        IsOvershadowedAppearance Gᶜᶜ H K' φ := by
    rw [hcc]; exact hnoover
  rcases hexapp with happ | happ
  · -- `L(H)` is an appearance of `K₄` in `G`
    obtain ⟨m, n, S, T, hstriation⟩ := hstr G hdegG happ
    obtain ⟨m', n', S', T', hmax, -⟩ :=
      MaximalStriationExists.exists_maximalStriation G S T hstriation
    obtain ⟨M, N, hcover, hdisj, hMloc, hNres⟩ :=
      exists_MN G hG hnoenl hnoover hnoovercompl m' n' S' T' hmax
    exact hcon (hmain G hG hnoenl hnoover hnoovercompl (h8 G happ) m' n' S' T' hmax
      M N hcover hdisj hMloc hNres)
  · -- *"by taking complements if necessary"*
    obtain ⟨m, n, S, T, hstriation⟩ := hstr Gᶜ hdegGc happ
    obtain ⟨m', n', S', T', hmax, -⟩ :=
      MaximalStriationExists.exists_maximalStriation Gᶜ S T hstriation
    obtain ⟨M, N, hcover, hdisj, hMloc, hNres⟩ :=
      exists_MN Gᶜ hGc hnoenlc hnoovercompl hnooverc' m' n' S' T' hmax
    exact hcon (concl_compl (hmain Gᶜ hGc hnoenlc hnoovercompl hnooverc' (h8 Gᶜ happ)
      m' n' S' T' hmax M N hcover hdisj hMloc hNres))

end Workspace.ProofLemmas.Thm96Assembly
