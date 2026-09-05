import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Infra
import Workspace.ProofLemmas.Thm192Claim2
import Workspace.ProofLemmas.Thm192Claim7
import Workspace.ProofLemmas.Thm192Claim8
import Workspace.ProofLemmas.Thm192Claim9YAdjX2Claim11
import Workspace.ProofLemmas.Thm192Claim9NotAdjX2
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.FirstTargetInducedPathInConnectedSet
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.NonCutVertices

/-!
# Running the printed proof of 19.2 at a hub vertex nonadjacent to `x₂`

This file is the assembly of `Workspace/Statements/S19/Thm_19_2.lean` — the interludes the
paper states without proof, between claims (4) and (11) — repeated verbatim for a vertex
`y` of the hub with the extra hypothesis `¬ G.Adj (x 2) y`, and stopped at claim (11)
rather than carried to the end.  The one conclusion needed here is claim (11)'s first
sentence,

> *"(11) `z` is not `Y₀`-complete …"*

Claim (9), used by three of the interludes, is taken from `Thm192Claim9NotAdjX2`, which is
exactly the branch of claim (9) that `¬ G.Adj (x 2) y` makes available; that is why this
file, and not `Workspace/Statements/S19/Thm_19_2.lean`, can be used by
`Thm192Claim9YAdjX2`.  Claim (10) is replaced by claim (8), which gives the same fact
`¬ G.Adj x₂ x₁` under `¬ G.Adj (x 2) y` and does not go through claim (9).

Everything below is a copy: the mathematics is the assembly documented in
`Workspace/Statements/S19/Thm_19_2.lean`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm192Claim9YAdjX2Rerun

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Bookkeeping about the frame and `A₁` -/

private theorem adj_z_x {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {t : ℕ}
    (hws : IsWheelSystem G z A₀ x t) {j : ℕ} (hj : j ≤ t) : G.Adj z (x j) :=
  hws.2.2.2.2.2.2 j hj

private theorem x_ne_z {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {t : ℕ}
    (hws : IsWheelSystem G z A₀ x t) {j : ℕ} (hj : j ≤ t) : x j ≠ z :=
  (hws.2.2.1 j hj).2

private theorem x_notMem_A1 {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {t : ℕ}
    (hws : IsWheelSystem G z A₀ x t) {j : ℕ} (hj : j ≤ t) :
    x j ∉ wheelSystemA G z A₀ x 1 :=
  fun h => Thm192Setup.wheelSystemA_no_z _ h (adj_z_x hws hj)

private theorem z_notMem_A1 {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {t : ℕ}
    (hws : IsWheelSystem G z A₀ x t) : z ∉ wheelSystemA G z A₀ x 1 := by
  intro h
  refine Thm192Setup.wheelSystemA_no_complete _ h ?_
  rw [Thm192Setup.wheelSystemX_one]
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl
  · exact adj_z_x hws (Nat.zero_le t)
  · exact adj_z_x hws hws.1

private theorem Y_notMem_A1 {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {Y : Set V}
    (hx0 : VertexComplete G (x 0) Y) (hx1 : VertexComplete G (x 1) Y) {w : V} (hw : w ∈ Y) :
    w ∉ wheelSystemA G z A₀ x 1 := by
  intro h
  refine Thm192Setup.wheelSystemA_no_complete _ h ?_
  rw [Thm192Setup.wheelSystemX_one]
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl
  · exact (hx0 w hw).symm
  · exact (hx1 w hw).symm

/-- The three vertices of the wheel system, and `z`, all lie outside `A₁`, hence outside
any `A ⊆ A₁`. -/
private theorem z_notMem_path {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    (hws : IsWheelSystem G z A₀ x 2) {A : Set V} (hAsub : A ⊆ wheelSystemA G z A₀ x 1)
    {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A) : z ∉ P := by
  intro hz
  by_cases h0 : z = x 0
  · exact x_ne_z hws (Nat.zero_le 2) h0.symm
  by_cases h1 : z = x 1
  · exact x_ne_z hws (by omega) h1.symm
  · exact z_notMem_A1 hws
      (hAsub (hPint z ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hz, h0, h1⟩)))

/-- *"let `C` be the hole `z-x₀-p₁-⋯-pₙ-x₁-z`"*. -/
private theorem hole_zP {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    (hws : IsWheelSystem G z A₀ x 2) {A : Set V} (hAsub : A ⊆ wheelSystemA G z A₀ x 1)
    {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A) (hPlen : 3 ≤ P.length) :
    IsHoleList G (z :: P) := by
  refine PrismBasics.isHoleList_of_path_add_vertex hP ?_ (adj_z_x hws (Nat.zero_le 2))
    (adj_z_x hws (by omega)) (z_notMem_path hws hAsub hP hPint) ?_
  · have := PathBasics.pathLength_eq P; omega
  · intro w hw
    exact Thm192Setup.wheelSystemA_no_z _ (hAsub (hPint w hw))

/-- The hole `z-x₀-p₁-⋯-pₙ-x₁-z` has at least six vertices: `n = 1` would make `p₁`
an `{x₀,x₁}`-complete vertex of `A₁`, and `n = 2` would make the hole odd. -/
private theorem P_len_ge_five {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V}
    {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2) {A : Set V}
    (hAsub : A ⊆ wheelSystemA G z A₀ x 1)
    {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A) (hPlen : 3 ≤ P.length) : 5 ≤ P.length := by
  have hBerge : Berge G := hG.1.1.1.1
  have hhole := hole_zP hws hAsub hP hPint hPlen
  have heven : Even (holeLength (z :: P)) := hBerge.1 _ hhole
  have hlen : holeLength (z :: P) = P.length + 1 := by simp [holeLength]
  rw [hlen] at heven
  by_contra hcon
  have hcase : P.length = 3 ∨ P.length = 4 := by omega
  rcases hcase with h3 | h4
  · -- `p₁` would be `{x₀,x₁}`-complete
    have hpos : 0 < P.length := by omega
    have h0 : P[0]'hpos = x 0 := PathBasics.getElem_zero_of_head? hP.2.1 hpos
    have hl : P[P.length - 1]'(by omega) = x 1 :=
      PathBasics.getElem_last_of_getLast? hP.2.2 hpos
    have hmem : (P[1]'(by omega)) ∈ SPGT.interior P :=
      PathBasics.getElem_mem_interior hP.1 (by omega) le_rfl (by omega)
    have hadj0 : G.Adj (x 0) (P[1]'(by omega)) := by
      have := PathBasics.path_adj_succ hP.1 (show 0 + 1 < P.length by omega)
      rwa [h0] at this
    have hadj1 : G.Adj (x 1) (P[1]'(by omega)) := by
      have := PathBasics.path_adj_succ hP.1 (show 1 + 1 < P.length by omega)
      have he : P[1 + 1]'(show 1 + 1 < P.length by omega) = x 1 := by
        rw [← hl]; congr 1; omega
      rw [he] at this
      exact this.symm
    refine Thm192Setup.wheelSystemA_no_complete _ (hAsub (hPint _ hmem)) ?_
    rw [Thm192Setup.wheelSystemX_one]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact hadj0.symm
    · exact hadj1.symm
  · rw [h4] at heven
    exact (Nat.not_even_iff_odd.mpr (by decide)) heven

/-! ### The interlude before (4) and the choice before (6)

PAPER: *"Let `x₀-p₁-⋯-pₙ-x₁` be a path from `x₀` to `x₁` with interior in `A`, and let `C`
be the hole `z-x₀-p₁-⋯-pₙ-x₁-z`."*  and  *"Let us choose `p₁,…,pₙ` and `C` such that either
`x₂` is `Y₀`-complete or `(C,Y₀)` is a wheel (this is possible by (2))."* -/

/-- *"Let `x₀-p₁-⋯-pₙ-x₁` be a path from `x₀` to `x₁` with interior in `A`"* — such a path
exists because `A` is connected and both `x₀, x₁` have neighbours in it. -/
private theorem exists_pathA {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    (hws : IsWheelSystem G z A₀ x 2) {Y : Set V} {y : V} {A : Set V}
    (hA : GoodA G z A₀ x Y y A) :
    ∃ P : List V, IsPathFrom G P (x 0) (x 1) ∧ 3 ≤ P.length ∧
      (∀ w ∈ SPGT.interior P, w ∈ A) := by
  obtain ⟨hAsub, hAconn, hA0, hA1, hA2, hAY, hAy⟩ := hA
  have hx0A : x 0 ∉ A := fun h => x_notMem_A1 hws (Nat.zero_le 2) (hAsub h)
  have hx1A : x 1 ∉ A := fun h => x_notMem_A1 hws (by omega) (hAsub h)
  have hne : x 0 ≠ x 1 := fun h => by
    have := hws.2.1 0 (by omega) 1 (by omega) h; omega
  have hnadj : ¬ G.Adj (x 0) (x 1) := Thm192Setup.x0_not_adj_x1 hws
  obtain ⟨P, hP, hPlen, hPint, -, -, -⟩ :=
    MinimalConnectedIsPath.exists_path_interior_attached hAconn hne hnadj hx0A hx1A hA0 hA1
  exact ⟨P, hP, hPlen, hPint⟩

/-- Transport of `IsWheel` along a re-listing of the rim with the same vertices and the
same length (used for the `x₀ ↔ x₁` symmetry, where the rim `z-x₀-P-x₁-z` is read backwards
as `z-x₁-P̄-x₀-z`). -/
private theorem isWheel_congr {G : SimpleGraph V} {W : Set V} {C D : List V}
    (hD : IsHoleList G D) (hlen : C.length = D.length) (hmem : ∀ v : V, v ∈ D ↔ v ∈ C)
    (h : IsWheel G C W) : IsWheel G D W := by
  obtain ⟨⟨-, hC6⟩, ⟨hWne, hWanti, hWdisj⟩, a, b, c, d, ha, hb, hc, hd, hab, hcd,
    hac, had, hbc, hbd⟩ := h
  refine ⟨⟨hD, ?_⟩, ⟨hWne, hWanti, ?_⟩, a, b, c, d, (hmem a).mpr ha, (hmem b).mpr hb,
    (hmem c).mpr hc, (hmem d).mpr hd, hab, hcd, hac, had, hbc, hbd⟩
  · simpa [holeLength, ← hlen] using hC6
  · intro v hv
    exact hWdisj v ((hmem v).mp hv)

/-- *"Let us choose `p₁,…,pₙ` and `C` such that either `x₂` is `Y₀`-complete or `(C,Y₀)` is
a wheel (this is possible by (2))."*

**The right disjunct carries a second conjunct**: `{p₁,…,pₙ}` contains *two distinct*
`Y₀`-complete vertices.  This is not decoration — it is the fact claims (6) and (10) need
(*"all other vertices of `Y` have at least two neighbours in `{p₁,…,pₙ}`"*), and it is
**not recoverable from `IsWheel G (z :: P) (Y \ {y})`**: `IsWheel` has no clause giving a
hub vertex a rim neighbour, and its two-disjoint-edges clause yields at most *one*
`Y₀`-complete interior vertex, since `z` absorbs one of the two edges.

The fact is available all the same, from the *other* conjunct of claim (2): the count
`2 ≤ #{Y₀-complete edges of P}`, converted by `Thm192Infra.two_complete_in_interior`.  The
paper cites claim (2) in exactly this form at claims (3) and (9) and shorthands it as
*"is a wheel"* only at (6) and (10); the shorthand is a citation slip in the exposition,
not a gap in the mathematics.  An earlier revision of this file destructured `hedges` and
then threw the second edge away via `Set.nonempty_of_ncard_ne_zero`, which is what made
(6) and (10) look unprovable.  Do not weaken it back.

The conjunct is attached to the **right disjunct only**.  That is sound because `Or.inr` is
produced solely in the branch where claim (2) returned its own right disjunct with
`Y₀ ≠ ∅`, and that branch returns claim (2)'s own `P` — the very path the edge count speaks
about.  The two `Or.inl` branches return an unrelated `P₀` with no edge data. -/
private theorem interludeChoice {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2)
    {Y : Set V} (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    {y : V} (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    {A : Set V} (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard) :
    ∃ P : List V, IsPathFrom G P (x 0) (x 1) ∧ (∀ w ∈ SPGT.interior P, w ∈ A) ∧
      3 ≤ P.length ∧
      (VertexComplete G (x 2) (Y \ {y}) ∨
        (IsWheel G (z :: P) (Y \ {y}) ∧
          ∃ c ∈ SPGT.interior P, ∃ d ∈ SPGT.interior P, c ≠ d ∧
            VertexComplete G c (Y \ {y}) ∧ VertexComplete G d (Y \ {y}))) := by
  obtain ⟨P₀, hP₀, hP₀len, hP₀int⟩ := exists_pathA hws hA
  have hAsub : A ⊆ wheelSystemA G z A₀ x 1 := hA.1
  have hne : x 0 ≠ x 1 := fun h => by
    have := hws.2.1 0 (by omega) 1 (by omega) h; omega
  have hnadj : ¬ G.Adj (x 0) (x 1) := Thm192Setup.x0_not_adj_x1 hws
  rcases Thm192Claim2.claim2 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA hAmin with
    hL | ⟨hzY, P, hP, hPint, hedges⟩
  · exact ⟨P₀, hP₀, hP₀int, hP₀len, Or.inl hL.1⟩
  by_cases hY0e : Y \ {y} = ∅
  · refine ⟨P₀, hP₀, hP₀int, hP₀len, Or.inl ?_⟩
    rw [hY0e]
    intro v hv
    exact absurd hv (Set.notMem_empty v)
  have hY0anti : AnticonnectedSet G (Y \ {y}) := hY0.resolve_left hY0e
  have hY0ne : (Y \ {y}).Nonempty := Set.nonempty_iff_ne_empty.mpr hY0e
  have hPlen : 3 ≤ P.length := MinimalConnectedIsPath.three_le_length_of_not_adj hP hne hnadj
  -- *"since `A` contains two `Y₀`-complete vertices"* (claims (3) and (9) cite (2) this
  -- way): claim (2)'s edge count, not the word "wheel", is what delivers the two vertices.
  have htwo : ∃ c ∈ SPGT.interior P, ∃ d ∈ SPGT.interior P, c ≠ d ∧
      VertexComplete G c (Y \ {y}) ∧ VertexComplete G d (Y \ {y}) :=
    Thm192Infra.two_complete_in_interior hws hAsub hP hPint hedges
  refine ⟨P, hP, hPint, hPlen, Or.inr ⟨?_, htwo⟩⟩
  have hhole : IsHoleList G (z :: P) := hole_zP hws hAsub hP hPint hPlen
  have hlen5 : 5 ≤ P.length := P_len_ge_five hG hws hAsub hP hPint hPlen
  have hzP : z ∉ P := z_notMem_path hws hAsub hP hPint
  -- the rim is disjoint from `Y₀`
  have hdisj : ∀ v ∈ z :: P, v ∉ Y \ {y} := by
    intro v hv hvY0
    rcases List.mem_cons.mp hv with heq | hvP
    · exact (hHyp.1 v hvY0.1).1 heq
    by_cases h0 : v = x 0
    · exact (hHyp.1 v hvY0.1).2.1 h0
    by_cases h1 : v = x 1
    · exact (hHyp.1 v hvY0.1).2.2.1 h1
    · exact Y_notMem_A1 hHyp.2.2.1 hHyp.2.2.2.1 hvY0.1
        (hAsub (hPint v ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hvP, h0, h1⟩)))
  -- one `Y₀`-complete edge inside `P` …
  have hSne : {e : Sym2 V | ∃ u ∈ P, ∃ v ∈ P, e = s(u, v) ∧
      EdgeComplete G (Y \ {y}) u v}.Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨e, u, huP, v, hvP, -, hedge⟩ := hSne
  -- … together with `z x₀` or `z x₁`, which are disjoint from it
  have hzu : z ≠ u := fun h => hzP (h ▸ huP)
  have hzv : z ≠ v := fun h => hzP (h ▸ hvP)
  have hx0P : x 0 ∈ P := (PathBasics.isPathFrom_ends_mem hP).1
  have hx1P : x 1 ∈ P := (PathBasics.isPathFrom_ends_mem hP).2
  have hedgeZ : ∀ w : V, (w = x 0 ∨ w = x 1) → EdgeComplete G (Y \ {y}) z w := by
    intro w hw
    rcases hw with rfl | rfl
    · exact ⟨adj_z_x hws (Nat.zero_le 2), fun q hq => hzY q hq.1,
        fun q hq => hHyp.2.2.1 q hq.1⟩
    · exact ⟨adj_z_x hws (by omega), fun q hq => hzY q hq.1,
        fun q hq => hHyp.2.2.2.1 q hq.1⟩
  have hlen6 : 6 ≤ holeLength (z :: P) := by simp only [holeLength, List.length_cons]; omega
  by_cases hc0 : x 0 = u ∨ x 0 = v
  · -- then `x₁ ∉ {u, v}`
    have h1u : x 1 ≠ u := by
      rintro rfl
      rcases hc0 with h | h
      · exact hne (h.trans rfl)
      · exact hnadj (by rw [h]; exact hedge.1.symm)
    have h1v : x 1 ≠ v := by
      rintro rfl
      rcases hc0 with h | h
      · exact hnadj (by rw [h]; exact hedge.1)
      · exact hne (h.trans rfl)
    exact ⟨⟨hhole, hlen6⟩, ⟨hY0ne, hY0anti, hdisj⟩,
      z, x 1, u, v, List.mem_cons_self, List.mem_cons_of_mem _ hx1P,
      List.mem_cons_of_mem _ huP, List.mem_cons_of_mem _ hvP,
      hedgeZ (x 1) (Or.inr rfl), hedge, hzu, hzv, h1u, h1v⟩
  · push_neg at hc0
    exact ⟨⟨hhole, hlen6⟩, ⟨hY0ne, hY0anti, hdisj⟩,
      z, x 0, u, v, List.mem_cons_self, List.mem_cons_of_mem _ hx0P,
      List.mem_cons_of_mem _ huP, List.mem_cons_of_mem _ hvP,
      hedgeZ (x 0) (Or.inl rfl), hedge, hzu, hzv, hc0.1, hc0.2⟩

/-! ### The interlude after (9): the vertex `f` -/

/-- The two ends of the path `x₀-p₁-⋯-pₙ-x₁` are attached to its interior. -/
private theorem path_ends_attached {G : SimpleGraph V} {P : List V} {u v : V}
    (hP : IsPathFrom G P u v) (hPlen : 3 ≤ P.length) :
    (∃ a ∈ SPGT.interior P, G.Adj u a) ∧ (∃ a ∈ SPGT.interior P, G.Adj v a) := by
  have hpos : 0 < P.length := by omega
  have h0 : P[0]'hpos = u := PathBasics.getElem_zero_of_head? hP.2.1 hpos
  have hl : P[P.length - 1]'(by omega) = v := PathBasics.getElem_last_of_getLast? hP.2.2 hpos
  refine ⟨⟨P[1]'(by omega), PathBasics.getElem_mem_interior hP.1 (by omega) le_rfl (by omega),
      ?_⟩, ⟨P[P.length - 2]'(by omega),
      PathBasics.getElem_mem_interior hP.1 (by omega) (by omega) (by omega), ?_⟩⟩
  · have := PathBasics.path_adj_succ hP.1 (show 0 + 1 < P.length by omega)
    rwa [h0] at this
  · have := PathBasics.path_adj_succ hP.1 (show (P.length - 2) + 1 < P.length by omega)
    have he : P[(P.length - 2) + 1]'(show (P.length - 2) + 1 < P.length by omega) = v := by
      rw [← hl]; congr 1; omega
    rw [he] at this
    exact this.symm

/-- *"By (7) and (9), `x₂` has no neighbour in `{p₁,…,pₙ}`."* -/
private theorem hx2_noP {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2)
    {Y : Set V} (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    {y : V} (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    {A : Set V} (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hcex : ¬ Thm192Setup.Concl192 G z A₀ x Y)
    {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A) (hPlen : 3 ≤ P.length)
    (hchoice : VertexComplete G (x 2) (Y \ {y}) ∨
      (IsWheel G (z :: P) (Y \ {y}) ∧
        ∃ c ∈ SPGT.interior P, ∃ d ∈ SPGT.interior P, c ≠ d ∧
          VertexComplete G c (Y \ {y}) ∧ VertexComplete G d (Y \ {y})))
    (h2y : ¬ G.Adj (x 2) y) :
    ∀ w ∈ SPGT.interior P, ¬ G.Adj (x 2) w := by
  intro w hw hadj
  obtain ⟨hnb0, hnb1⟩ := path_ends_attached hP hPlen
  have hEq : {v : V | v ∈ SPGT.interior P} = A :=
    Thm192Claim9NotAdjX2.claim9_of_not_x2_adj_y G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA hAmin hcex h2y
      {v : V | v ∈ SPGT.interior P} (fun v hv => hPint v hv)
      (MinimalConnectedIsPath.connectedSet_interior hP) hnb0 hnb1 ⟨w, hw, hadj⟩
  obtain ⟨a, haA, hya⟩ := hA.2.2.2.2.2.2
  rw [← hEq] at haA
  exact Thm192Claim7.claim7 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA hAmin hcex
    P hP hPint hPlen hchoice ⟨⟨w, hw, hadj⟩, ⟨a, haA, hya⟩⟩

/-- *"From (7) and (9), it follows that there exists `f ∈ A` such that `A \ {f}` is
connected, `f` does not belong to `C`, and `f` is the unique neighbour of `x₂` in `A`."* -/
private theorem interludeF {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2)
    {Y : Set V} (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    {y : V} (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    {A : Set V} (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hcex : ¬ Thm192Setup.Concl192 G z A₀ x Y)
    {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A) (hPlen : 3 ≤ P.length)
    (hx2noP : ∀ w ∈ SPGT.interior P, ¬ G.Adj (x 2) w)
    (h2y : ¬ G.Adj (x 2) y) :
    ∃ f : V, f ∈ A ∧ ConnectedSet G (A \ {f}) ∧ f ∉ P ∧ G.Adj (x 2) f ∧
      (∀ a ∈ A, G.Adj (x 2) a → a = f) := by
  obtain ⟨hAsub, hAconn, hA0, hA1, hA2, hAY, hAy⟩ := hA
  set B : Set V := {v : V | v ∈ SPGT.interior P} with hBdef
  have hBsub : B ⊆ A := fun v hv => hPint v hv
  have hBconn : ConnectedSet G B := MinimalConnectedIsPath.connectedSet_interior hP
  obtain ⟨hnb0, hnb1⟩ := path_ends_attached hP hPlen
  have hABne : (A ∩ B).Nonempty := by
    obtain ⟨a, haB, -⟩ := hnb0
    exact ⟨a, hBsub haB, haB⟩
  have hx2B : x 2 ∉ B := fun h => x_notMem_A1 hws (by omega) (hAsub (hBsub h))
  obtain ⟨p, hpAB, R, hR, hRpos, hRmem, hRB⟩ :=
    FirstTargetInducedPathInConnectedSet.firstTargetInducedPathInConnectedSet G A B (x 2)
      hAconn hA2 hABne hx2B
  have hRlen2 : 2 ≤ R.length := by have := PathBasics.pathLength_eq R; omega
  have hRnd : R.Nodup := PathBasics.path_nodup hR.1
  have hR0 : R[0]'(by omega) = x 2 := PathBasics.getElem_zero_of_head? hR.2.1 (by omega)
  have hRlast : R[R.length - 1]'(by omega) = p :=
    PathBasics.getElem_last_of_getLast? hR.2.2 (by omega)
  set f : V := R[1]'(by omega) with hfdef
  have hfadj : G.Adj (x 2) f := by
    have := PathBasics.path_adj_succ hR.1 (show 0 + 1 < R.length by omega)
    rwa [hR0] at this
  have hfmemR : f ∈ R := List.getElem_mem _
  have hfne2 : f ≠ x 2 := by
    rw [hfdef, ← hR0]
    exact PathBasics.path_ne_of_ne_index hR.1 (by omega) (by omega) (by omega)
  have hfA : f ∈ A := hRmem f hfmemR hfne2
  have hfB : f ∉ B := fun h => hx2noP f h hfadj
  have hfp : f ≠ p := fun h => hfB ((hRB f hfmemR).mpr h)
  have hpB : p ∈ B := hpAB.2
  have hpR : p ∈ R := by
    rw [← hRlast]; exact List.getElem_mem _
  have hpne2 : p ≠ x 2 := fun h => hx2B (h ▸ hpB)
  have hRlen3 : 3 ≤ R.length := by
    by_contra hcon
    have h2 : R.length = 2 := by omega
    exact hfp (by rw [hfdef, ← hRlast]; congr 1; omega)
  -- membership in the two tails of `R`
  have htake1 : R.take 1 = [x 2] := by
    rw [List.take_one, hR.2.1]; rfl
  have htake2 : R.take 2 = [x 2, f] := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, List.take_succ, htake1,
      List.getElem?_eq_getElem (show 1 < R.length by omega)]
    rfl
  have hmem1 : ∀ a : V, a ∈ R.drop 1 ↔ (a ∈ R ∧ a ≠ x 2) := by
    intro a
    constructor
    · intro ha
      have hdisj : ∀ u ∈ R.take 1, ∀ v ∈ R.drop 1, u ≠ v := by
        have hnd := hRnd
        rw [← List.take_append_drop 1 R] at hnd
        exact (List.nodup_append.mp hnd).2.2
      refine ⟨(List.drop_sublist 1 R).subset ha, ?_⟩
      intro hc
      exact hdisj (x 2) (by rw [htake1]; simp) _ ha hc.symm
    · rintro ⟨ha, hane⟩
      have : a ∈ R.take 1 ++ R.drop 1 := by rwa [List.take_append_drop]
      rcases List.mem_append.mp this with h | h
      · rw [htake1] at h; simp at h; exact absurd h hane
      · exact h
  have hmem2 : ∀ a : V, a ∈ R.drop 2 ↔ (a ∈ R ∧ a ≠ x 2 ∧ a ≠ f) := by
    intro a
    constructor
    · intro ha
      have haR : a ∈ R := (List.drop_sublist 2 R).subset ha
      have hdisj : ∀ u ∈ R.take 2, ∀ v ∈ R.drop 2, u ≠ v := by
        have hnd := hRnd
        rw [← List.take_append_drop 2 R] at hnd
        exact (List.nodup_append.mp hnd).2.2
      refine ⟨haR, ?_, ?_⟩
      · intro hc; exact hdisj (x 2) (by rw [htake2]; simp) _ ha hc.symm
      · intro hc; exact hdisj f (by rw [htake2]; simp) _ ha hc.symm
    · rintro ⟨ha, h2, hf⟩
      have : a ∈ R.take 2 ++ R.drop 2 := by rwa [List.take_append_drop]
      rcases List.mem_append.mp this with h | h
      · rw [htake2] at h
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
        rcases h with h | h
        · exact absurd h h2
        · exact absurd h hf
      · exact h
  have hR1conn : ConnectedSet G {v : V | v ∈ R.drop 1} :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (PathBasics.isPathList_drop hR.1 (by omega))
  have hR2conn : ConnectedSet G {v : V | v ∈ R.drop 2} :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (PathBasics.isPathList_drop hR.1 (by omega))
  have hfdrop1 : f ∈ R.drop 1 := (hmem1 f).mpr ⟨hfmemR, hfne2⟩
  have hpdrop1 : p ∈ R.drop 1 := (hmem1 p).mpr ⟨hpR, hpne2⟩
  have hpdrop2 : p ∈ R.drop 2 := (hmem2 p).mpr ⟨hpR, hpne2, fun h => hfp h.symm⟩
  -- `F = interior(P) ∪ (R \ x₂)` is connected, lies in `A`, and catches all of `x₀,x₁,x₂`
  have hFconn : ConnectedSet G (B ∪ {v : V | v ∈ R.drop 1}) :=
    ConnectedSetUnionAttach.connectedSet_union hBconn hR1conn (Or.inl ⟨p, hpB, hpdrop1⟩)
  have hFsub : B ∪ {v : V | v ∈ R.drop 1} ⊆ A := by
    rintro v (hv | hv)
    · exact hBsub hv
    · exact hRmem v ((hmem1 v).mp hv).1 ((hmem1 v).mp hv).2
  have hFeq : B ∪ {v : V | v ∈ R.drop 1} = A := by
    refine Thm192Claim9NotAdjX2.claim9_of_not_x2_adj_y G hG z A₀ hframe x hws Y hHyp ih y
      hyY hyz hY0 A ⟨hAsub, hAconn, hA0, hA1, hA2, hAY, hAy⟩ hAmin hcex h2y _ hFsub hFconn
      ?_ ?_ ?_
    · obtain ⟨a, haB, hadj⟩ := hnb0
      exact ⟨a, Or.inl haB, hadj⟩
    · obtain ⟨a, haB, hadj⟩ := hnb1
      exact ⟨a, Or.inl haB, hadj⟩
    · exact ⟨f, Or.inr hfdrop1, hfadj⟩
  -- uniqueness of `f`
  have huniq : ∀ a ∈ A, G.Adj (x 2) a → a = f := by
    intro a haA hadj
    rw [← hFeq] at haA
    rcases haA with hv | hv
    · exact absurd hadj (hx2noP a hv)
    · obtain ⟨haR, -⟩ := (hmem1 a).mp hv
      obtain ⟨k, hk, hka⟩ := List.mem_iff_getElem.mp haR
      have hadj' : G.Adj (R[0]'(by omega)) (R[k]'hk) := by rw [hR0, hka]; exact hadj
      have hk1 : k = 1 := by
        rcases (PathBasics.path_adj_iff hR.1 (show 0 < R.length by omega) hk).mp hadj' with h | h
        · omega
        · omega
      rw [hfdef, ← hka]
      congr 1
  -- `A \ {f}` is connected
  have hAf : A \ {f} = B ∪ {v : V | v ∈ R.drop 2} := by
    ext a
    constructor
    · rintro ⟨haA, haf⟩
      rw [← hFeq] at haA
      rcases haA with hv | hv
      · exact Or.inl hv
      · obtain ⟨haR, hane⟩ := (hmem1 a).mp hv
        exact Or.inr ((hmem2 a).mpr ⟨haR, hane, by simpa using haf⟩)
    · rintro (hv | hv)
      · exact ⟨hBsub hv, by simp only [Set.mem_singleton_iff]; rintro rfl; exact hfB hv⟩
      · obtain ⟨haR, hane, hanef⟩ := (hmem2 a).mp hv
        exact ⟨hRmem a haR hane, by simpa using hanef⟩
  refine ⟨f, hfA, ?_, ?_, hfadj, huniq⟩
  · rw [hAf]
    exact ConnectedSetUnionAttach.connectedSet_union hBconn hR2conn (Or.inl ⟨p, hpB, hpdrop2⟩)
  · intro hfP
    have hf0 : f ≠ x 0 := by
      intro h; exact x_notMem_A1 hws (Nat.zero_le 2) (h ▸ hAsub hfA)
    have hf1 : f ≠ x 1 := by
      intro h; exact x_notMem_A1 hws (by omega) (h ▸ hAsub hfA)
    exact hfB ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hfP, hf0, hf1⟩)

/-! ### The interlude before (11): *"From (9) one of `x₀, x₁` has a unique neighbour in `A`"* -/

private theorem interludeUnique {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2)
    {Y : Set V} (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    {y : V} (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    {A : Set V} (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hcex : ¬ Thm192Setup.Concl192 G z A₀ x Y)
    {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A) (hPlen : 3 ≤ P.length)
    {f : V} (hfA : f ∈ A) (hfP : f ∉ P)
    (h2y : ¬ G.Adj (x 2) y) :
    (∃ f₁, f₁ ∈ A ∧ G.Adj (x 0) f₁ ∧ ∀ a ∈ A, G.Adj (x 0) a → a = f₁) ∨
    (∃ f₁, f₁ ∈ A ∧ G.Adj (x 1) f₁ ∧ ∀ a ∈ A, G.Adj (x 1) a → a = f₁) := by
  obtain ⟨hnb0, hnb1⟩ := path_ends_attached hP hPlen
  -- `A` has at least two vertices: `f ∉ P`, while `p₁ ∈ P`
  have hAns : ¬ A.Subsingleton := by
    obtain ⟨a, haInt, -⟩ := hnb0
    intro hsub
    exact hfP (hsub hfA (hPint a haInt) ▸ PathBasics.interior_subset haInt)
  -- by (9), every non-cut vertex of `A` is the unique neighbour in `A` of one of `x₀,x₁,x₂`
  have key : ∀ v ∈ A, ConnectedSet G (A \ {v}) →
      (G.Adj (x 0) v ∧ ∀ a ∈ A, G.Adj (x 0) a → a = v) ∨
      (G.Adj (x 1) v ∧ ∀ a ∈ A, G.Adj (x 1) a → a = v) ∨
      (G.Adj (x 2) v ∧ ∀ a ∈ A, G.Adj (x 2) a → a = v) := by
    intro v hvA hconn
    by_cases h0 : ∃ a ∈ A \ {v}, G.Adj (x 0) a
    · by_cases h1 : ∃ a ∈ A \ {v}, G.Adj (x 1) a
      · by_cases h2 : ∃ a ∈ A \ {v}, G.Adj (x 2) a
        · exfalso
          have heq : A \ {v} = A :=
            Thm192Claim9NotAdjX2.claim9_of_not_x2_adj_y G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA hAmin hcex h2y
              (A \ {v}) Set.diff_subset hconn h0 h1 h2
          have hvv : v ∈ A \ {v} := by rw [heq]; exact hvA
          exact hvv.2 rfl
        · push_neg at h2
          obtain ⟨a, haA, hadj⟩ := hA.2.2.2.2.1
          have hav : a = v := by
            by_contra hne
            exact h2 a ⟨haA, by simpa using hne⟩ hadj
          exact Or.inr (Or.inr ⟨hav ▸ hadj, fun b hbA hbadj => by
            by_contra hne; exact h2 b ⟨hbA, by simpa using hne⟩ hbadj⟩)
      · push_neg at h1
        obtain ⟨a, haA, hadj⟩ := hA.2.2.2.1
        have hav : a = v := by
          by_contra hne
          exact h1 a ⟨haA, by simpa using hne⟩ hadj
        exact Or.inr (Or.inl ⟨hav ▸ hadj, fun b hbA hbadj => by
          by_contra hne; exact h1 b ⟨hbA, by simpa using hne⟩ hbadj⟩)
    · push_neg at h0
      obtain ⟨a, haA, hadj⟩ := hA.2.2.1
      have hav : a = v := by
        by_contra hne
        exact h0 a ⟨haA, by simpa using hne⟩ hadj
      exact Or.inl ⟨hav ▸ hadj, fun b hbA hbadj => by
        by_contra hne; exact h0 b ⟨hbA, by simpa using hne⟩ hbadj⟩
  obtain ⟨a, haA, b, hbA, hab, hAa, hAb⟩ := NonCutVertices.exists_two_noncut hA.2.1 hAns
  rcases key a haA hAa with ha | ha | ha
  · exact Or.inl ⟨a, haA, ha⟩
  · exact Or.inr ⟨a, haA, ha⟩
  · rcases key b hbA hAb with hb | hb | hb
    · exact Or.inl ⟨b, hbA, hb⟩
    · exact Or.inr ⟨b, hbA, hb⟩
    · exact absurd (ha.2 b hbA hb.1).symm hab

/-! ### The closing interlude, stopped at claim (11) -/

private theorem endgameAt {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2)
    {Y : Set V} (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    {y : V} (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    {A : Set V} (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hcex : ¬ Thm192Setup.Concl192 G z A₀ x Y)
    {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A) (hPlen : 3 ≤ P.length)
    (hchoice : VertexComplete G (x 2) (Y \ {y}) ∨
      (IsWheel G (z :: P) (Y \ {y}) ∧
        ∃ c ∈ SPGT.interior P, ∃ d ∈ SPGT.interior P, c ≠ d ∧
          VertexComplete G c (Y \ {y}) ∧ VertexComplete G d (Y \ {y})))
    {f : V} (hfA : f ∈ A) (hfconn : ConnectedSet G (A \ {f})) (hfC : f ∉ P)
    (hfadj : G.Adj (x 2) f) (hfuniq : ∀ a ∈ A, G.Adj (x 2) a → a = f)
    (hx2noP : ∀ w ∈ SPGT.interior P, ¬ G.Adj (x 2) w)
    {f₁ : V} (hf₁A : f₁ ∈ A) (hf₁adj : G.Adj (x 1) f₁)
    (hf₁uniq : ∀ a ∈ A, G.Adj (x 1) a → a = f₁)
    (h2y : ¬ G.Adj (x 2) y) : ¬ VertexComplete G z (Y \ {y}) := by
  have hAsub : A ⊆ wheelSystemA G z A₀ x 1 := hA.1
  -- *"and in particular `f ≠ f₁`"*: `f₁ = pₙ ∈ C`, while `f ∉ C`
  obtain ⟨-, hnb1⟩ := path_ends_attached hP hPlen
  obtain ⟨q, hqInt, hqadj⟩ := hnb1
  have hf₁P : f₁ ∈ P := by
    rw [← hf₁uniq q (hPint q hqInt) hqadj]
    exact PathBasics.interior_subset hqInt
  have hff₁ : f ≠ f₁ := fun h => hfC (by rw [h]; exact hf₁P)
  -- *"Let `Q` be a path in `A` between `f, f₁`"*
  obtain ⟨Q, hQ, hQA⟩ := InducedPathExtraction.exists_isPathFrom_of_connected hA.2.1 hfA hf₁A
  have hQlen : 0 < Q.length := PathBasics.path_length_pos hQ.1
  have hx2x1 : ¬ G.Adj (x 2) (x 1) :=
    (Thm192Claim8.claim8 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA hAmin hcex
      h2y).2
  have hx2ne1 : x 2 ≠ x 1 := by
    intro h; have := hws.2.1 2 (by omega) 1 (by omega) h; omega
  have hx2Q : x 2 ∉ Q := fun h => x_notMem_A1 hws (by omega) (hAsub (hQA _ h))
  have hx1Q : x 1 ∉ Q := fun h => x_notMem_A1 hws (by omega) (hAsub (hQA _ h))
  have hpath : IsPathFrom G (x 2 :: (Q ++ [x 1])) (x 2) (x 1) :=
    PathAttach.isPathFrom_cons_concat hQ hfadj hf₁adj hx2x1 hx2ne1 hx2Q hx1Q
      (fun w hw hwf hadj => hwf (hfuniq w (hQA w hw) hadj))
      (fun w hw hwf hadj => hwf (hf₁uniq w (hQA w hw) hadj))
  have hint : SPGT.interior (x 2 :: (Q ++ [x 1])) = Q := by
    simp [SPGT.interior]
  -- *"so `z-x₂-q₁-⋯-q_k-x₁-z` is a hole (`C₁` say)"*
  have hC₁ : IsHoleList G (z :: x 2 :: (Q ++ [x 1])) := by
    refine PrismBasics.isHoleList_of_path_add_vertex hpath ?_ (adj_z_x hws (by omega))
      (adj_z_x hws (by omega)) ?_ ?_
    · rw [PathAttach.pathLength_cons_append_singleton]; omega
    · intro hz
      simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil,
        or_false] at hz
      rcases hz with h | h | h
      · exact x_ne_z hws (show 2 ≤ 2 by omega) h.symm
      · exact z_notMem_A1 hws (hAsub (hQA z h))
      · exact x_ne_z hws (show 1 ≤ 2 by omega) h.symm
    · intro w hw
      rw [hint] at hw
      exact Thm192Setup.wheelSystemA_no_z _ (hAsub (hQA w hw))
  exact (Thm192Claim9YAdjX2Claim11.claim11 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0
    A hA hAmin hcex P hP hPint hPlen hchoice f hfA hfconn hfC hfadj hfuniq f₁ hf₁A hf₁adj
    hf₁uniq hx2noP hff₁ Q hQ hQA hC₁ h2y).1


private def sw (x : ℕ → V) : ℕ → V :=
  fun n => if n = 0 then x 1 else if n = 1 then x 0 else x n

private theorem sw_zero (x : ℕ → V) : sw x 0 = x 1 := by simp [sw]

private theorem sw_one (x : ℕ → V) : sw x 1 = x 0 := by simp [sw]

private theorem sw_two (x : ℕ → V) : sw x 2 = x 2 := by simp [sw]

private theorem sw_apply (x : ℕ → V) (n : ℕ) :
    sw x n = x (if n = 0 then 1 else if n = 1 then 0 else n) := by
  simp only [sw]; split_ifs <;> rfl

private theorem sw_sw (x : ℕ → V) : sw (sw x) = x := by
  funext n
  by_cases h0 : n = 0
  · subst h0; rw [sw_zero, sw_one]
  by_cases h1 : n = 1
  · subst h1; rw [sw_one, sw_zero]
  · rw [sw_apply, sw_apply]
    simp [h0, h1]

private theorem sw_X1 (x : ℕ → V) : wheelSystemX (sw x) 1 = wheelSystemX x 1 := by
  rw [Thm192Setup.wheelSystemX_one, Thm192Setup.wheelSystemX_one, sw_zero, sw_one]
  exact Set.pair_comm _ _

private theorem sw_A1 (G : SimpleGraph V) (z : V) (A₀ : Set V) (x : ℕ → V) :
    wheelSystemA G z A₀ (sw x) 1 = wheelSystemA G z A₀ x 1 := by
  simp only [wheelSystemA, sw_X1]

private theorem sw_ws {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    (hws : IsWheelSystem G z A₀ x 2) : IsWheelSystem G z A₀ (sw x) 2 := by
  obtain ⟨h1, hinj, hout, ⟨he0, he1, hnc⟩, hcond2, hcond3, hz⟩ := hws
  refine ⟨h1, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro j hj k hk hjk
    rw [sw_apply, sw_apply] at hjk
    have := hinj _ (by split_ifs <;> omega) _ (by split_ifs <;> omega) hjk
    split_ifs at this <;> omega
  · intro j hj
    rw [sw_apply]
    exact hout _ (by split_ifs <;> omega)
  · rw [sw_zero]; exact he1
  · rw [sw_one]; exact he0
  · intro a ha hcon
    refine hnc a ha ?_
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    refine hcon v ?_
    simp only [sw_zero, sw_one, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · intro i hi2 hi2'
    have hi : i = 2 := by omega
    subst hi
    obtain ⟨B, hB0, hBc, ⟨b, hbB, hadj⟩, hBz, hBX⟩ := hcond2 2 (by omega) (by omega)
    exact ⟨B, hB0, hBc, ⟨b, hbB, by rw [sw_two]; exact hadj⟩, hBz,
      by simp only [show (2 : ℕ) - 1 = 1 from rfl, sw_X1]; exact hBX⟩
  · intro i hi1 hi2
    interval_cases i
    · intro hcon
      refine hcond3 1 (by omega) (by omega) ?_
      intro v hv
      obtain ⟨j, hj, rfl⟩ := hv
      have hj0 : j = 0 := by omega
      subst hj0
      have h := hcon (sw x 0) ⟨0, le_rfl, rfl⟩
      rw [sw_zero, sw_one] at h
      exact h.symm
    · simp only [sw_two, show (2 : ℕ) - 1 = 1 from rfl, sw_X1]
      exact hcond3 2 (by omega) (by omega)
  · intro j hj
    rw [sw_apply]
    exact hz _ (by split_ifs <;> omega)

private theorem sw_hyp {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {Y : Set V}
    (h : Hyp192 G z A₀ x Y) : Hyp192 G z A₀ (sw x) Y := by
  obtain ⟨hsub, hanti, h0, h1, h2, hnb⟩ := h
  refine ⟨?_, hanti, ?_, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨ha, hb, hc, hd⟩ := hsub w hw
    exact ⟨ha, by rw [sw_zero]; exact hc, by rw [sw_one]; exact hb, by rw [sw_two]; exact hd⟩
  · rw [sw_zero]; exact h1
  · rw [sw_one]; exact h0
  · rw [sw_two]; exact h2
  · intro w hw hnadj
    rw [sw_two] at hnadj
    rw [sw_A1]
    exact hnb w hw hnadj

private theorem sw_concl {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {Y : Set V}
    (h : Concl192 G z A₀ x Y) : Concl192 G z A₀ (sw x) Y := by
  obtain ⟨hz, C, hW, h0, h1, hzC, hCsub⟩ := h
  refine ⟨hz, C, hW, by rw [sw_zero]; exact h1, by rw [sw_one]; exact h0, hzC, ?_⟩
  rw [sw_zero, sw_one, sw_A1]
  intro v hv
  rcases hCsub hv with hh | hh
  · refine Or.inl ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh ⊢
    tauto
  · exact Or.inr hh

private theorem sw_goodA {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {Y : Set V}
    {y : V} {A : Set V} (h : GoodA G z A₀ x Y y A) : GoodA G z A₀ (sw x) Y y A := by
  obtain ⟨hsub, hconn, h0, h1, h2, hY, hy⟩ := h
  exact ⟨by rw [sw_A1]; exact hsub, hconn, by rw [sw_zero]; exact h1,
    by rw [sw_one]; exact h0, by rw [sw_two]; exact h2,
    by simpa only [sw_two] using hY, hy⟩

/-! ### The printed argument from claim (2) to claim (11), for a hub vertex nonadjacent
to `x₂` -/

/-- **Claim (11)'s first sentence**, *"`z` is not `Y₀`-complete"*, for a vertex `y` of the
hub that is nonadjacent to `x₂` and a cardinality-minimal `GoodA` set for it.

The proof is the assembly of `Workspace/Statements/S19/Thm_19_2.lean` (`core`) as far as
claim (11): the choice of `p₁,…,pₙ` and `C` before (6), *"by (7) and (9), `x₂` has no
neighbour in `{p₁,…,pₙ}`"*, the two interludes after (9), the path `Q` and the hole `C₁`
before (11), and then claim (11) itself. -/
theorem z_not_Y0_complete {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2)
    {Y : Set V} (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    {y : V} (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    {A : Set V} (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hcex : ¬ Thm192Setup.Concl192 G z A₀ x Y)
    (h2y : ¬ G.Adj (x 2) y) :
    ¬ VertexComplete G z (Y \ {y}) := by
  obtain ⟨P, hP, hPint, hPlen, hchoice⟩ :=
    interludeChoice hG hframe hws hHyp ih hyY hyz hY0 hA hAmin
  -- *"By (7) and (9), `x₂` has no neighbour in `{p₁,…,pₙ}`"*
  have hx2noP :=
    hx2_noP hG hframe hws hHyp ih hyY hyz hY0 hA hAmin hcex hP hPint hPlen hchoice h2y
  -- *"From (7) and (9), it follows that there exists `f ∈ A` …"*
  obtain ⟨f, hfA, hfconn, hfP, hfadj, hfuniq⟩ :=
    interludeF hG hframe hws hHyp ih hyY hyz hY0 hA hAmin hcex hP hPint hPlen hx2noP h2y
  -- *"From (9) one of `x₀, x₁` has a unique neighbour in `A` …"*
  rcases interludeUnique hG hframe hws hHyp ih hyY hyz hY0 hA hAmin hcex hP hPint hPlen
    hfA hfP h2y with h0 | h1
  · -- *"… and from the symmetry we may assume it is `x₁`"*
    obtain ⟨f₁, hf₁A, hf₁adj, hf₁uniq⟩ := h0
    have hwsS : IsWheelSystem G z A₀ (sw x) 2 := sw_ws hws
    have hHypS : Hyp192 G z A₀ (sw x) Y := sw_hyp hHyp
    have ihS : (∀ Y' : Set V, Y'.ncard < Y.ncard →
        Hyp192 G z A₀ (sw x) Y' → Concl192 G z A₀ (sw x) Y') ∧
        Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard := by
      refine ⟨?_, ih.2⟩
      intro Y' hlt hH
      have hH' : Hyp192 G z A₀ x Y' := by
        have hh := sw_hyp hH
        rwa [sw_sw] at hh
      exact sw_concl (ih.1 Y' hlt hH')
    have hAS : GoodA G z A₀ (sw x) Y y A := sw_goodA hA
    have hAminS : ∀ B : Set V, GoodA G z A₀ (sw x) Y y B → A.ncard ≤ B.ncard := by
      intro B hB
      refine hAmin B ?_
      have hh := sw_goodA hB
      rwa [sw_sw] at hh
    have hcexS : ¬ Thm192Setup.Concl192 G z A₀ (sw x) Y := by
      intro hcon
      have hh := sw_concl hcon
      rw [sw_sw] at hh
      exact hcex hh
    have hPS : IsPathFrom G P.reverse (sw x 0) (sw x 1) := by
      rw [sw_zero, sw_one]; exact PathBasics.isPathFrom_reverse hP
    have hPintS : ∀ w ∈ SPGT.interior P.reverse, w ∈ A := fun w hw =>
      hPint w (PathBasics.mem_interior_reverse.mp hw)
    have hPlenS : 3 ≤ P.reverse.length := by simpa using hPlen
    -- The two `Y₀`-complete interior vertices travel with the wheel: reversing `P` permutes
    -- its interior (`PathBasics.mem_interior_reverse`), exactly as `hPintS` above.
    have hchoiceS : VertexComplete G (sw x 2) (Y \ {y}) ∨
        (IsWheel G (z :: P.reverse) (Y \ {y}) ∧
          ∃ c ∈ SPGT.interior P.reverse, ∃ d ∈ SPGT.interior P.reverse, c ≠ d ∧
            VertexComplete G c (Y \ {y}) ∧ VertexComplete G d (Y \ {y})) := by
      rcases hchoice with h | ⟨h, c, hcI, d, hdI, hcd, hcY, hdY⟩
      · exact Or.inl (by rw [sw_two]; exact h)
      · exact Or.inr ⟨isWheel_congr (hole_zP hwsS hAS.1 hPS hPintS hPlenS) (by simp)
          (fun v => by simp) h,
          c, PathBasics.mem_interior_reverse.mpr hcI,
          d, PathBasics.mem_interior_reverse.mpr hdI, hcd, hcY, hdY⟩
    have hfCS : f ∉ P.reverse := by simpa using hfP
    have hfadjS : G.Adj (sw x 2) f := by rw [sw_two]; exact hfadj
    have hfuniqS : ∀ a ∈ A, G.Adj (sw x 2) a → a = f := by
      intro a ha hadj; rw [sw_two] at hadj; exact hfuniq a ha hadj
    have hx2noPS : ∀ w ∈ SPGT.interior P.reverse, ¬ G.Adj (sw x 2) w := by
      intro w hw
      rw [sw_two]
      exact hx2noP w (PathBasics.mem_interior_reverse.mp hw)
    have hf₁adjS : G.Adj (sw x 1) f₁ := by rw [sw_one]; exact hf₁adj
    have hf₁uniqS : ∀ a ∈ A, G.Adj (sw x 1) a → a = f₁ := by
      intro a ha hadj; rw [sw_one] at hadj; exact hf₁uniq a ha hadj
    exact endgameAt hG hframe hwsS hHypS ihS hyY hyz hY0 hAS hAminS hcexS hPS hPintS hPlenS
      hchoiceS hfA hfconn hfCS hfadjS hfuniqS hx2noPS hf₁A hf₁adjS hf₁uniqS
      (by rw [sw_two]; exact h2y)
  · obtain ⟨f₁, hf₁A, hf₁adj, hf₁uniq⟩ := h1
    exact endgameAt hG hframe hws hHyp ih hyY hyz hY0 hA hAmin hcex hP hPint hPlen hchoice
      hfA hfconn hfP hfadj hfuniq hx2noP hf₁A hf₁adj hf₁uniq h2y

end Workspace.ProofLemmas.Thm192Claim9YAdjX2Rerun
