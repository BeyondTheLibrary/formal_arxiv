import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes

/-!
# Setup for the proof of 19.2 — the `wheelSystemA` API and the two extremal choices

The printed proof of 19.2 (published *Annals* version, printed p. 118) opens with

> *"If possible, choose `Y` not satisfying the theorem, with `|Y|` minimum.  For fixed
> `Y` choose `A ⊆ A₁` minimal with the properties that*
>
> * *`A` is connected*
> * *`x₀, x₁, x₂` all have neighbours in `A`, and*
> * *every vertex in `Y` that is nonadjacent to `x₂` has a neighbour in `A`.*
>
> *It follows from the hypotheses that `A, Y` are both nonempty."*

and then derives a contradiction through twelve numbered claims.  This module carries
everything that argument needs *before* claim (1): the bookkeeping about
`A₁ = wheelSystemA G z A₀ x 1` that the paper leaves entirely implicit, the two extremal
choices, and the `Hyp192` / `Concl192` packaging of the hypotheses and conclusion of 19.2.

## The `wheelSystemA` API

`wheelSystemA G z A₀ x i` is the paper's `Aᵢ`: the union of all sets `A` with `A₀ ⊆ A`,
`A` connected, `A` containing no neighbour of `z`, and `A` containing no `Xᵢ`-complete
vertex.  Nothing in the project had any API for it; §§19–22 all need one.

* `mem_wheelSystemA` / `subset_wheelSystemA` — the two directions of the `⋃₀`.
* `wheelSystemA_no_z`, `wheelSystemA_no_complete` — the two *pointwise* clauses of the
  family survive the union.  In particular **`z` has no neighbour anywhere in `Aᵢ`**,
  which is what forces a hole through `z` with rim in `{x₀,x₁,z} ∪ A₁` to have `x₀, x₁`
  as `z`'s two rim-neighbours.
* `A0_subset_A1`, `A1_connected`, `x0_nb_A1`, `x1_nb_A1`, `x2_nb_A1` — `A₁` is itself a
  member of the family and satisfies every property the paper requires of `A`.
* `x0_not_adj_x1` — condition 3 of a wheel system at `i = 1` says exactly that `x₀x₁` is
  not an edge; used constantly in §19 to make `z-x₀-P-x₁-z` a hole.

## Reordering of the two printed extremal choices

The printed text chooses `A` *before* claim (1), and then asserts inside (1) that the
vertex `y` it produces *"has a neighbour in `A`"*.  That step is not available at that
point: the minimality of `|Y|` gives a wheel `(C, Y \ {y₂})` whose rim lies in
`{x₀,x₁,z} ∪ A₁`, so it yields a `Y \ {y₂}`-complete vertex in `A₁`, **not** in the
minimal `A ⊆ A₁`.  The repair — which is what claim (3) presupposes, since (3) lists `y`
alongside `x₀,x₁,x₂` among the vertices that `F` must have neighbours of — is to prove (1)
with `A₁` in place of `A` first, and only then to choose `A ⊆ A₁` minimal subject to the
printed properties **and** *"`y` has a neighbour in `A`"* (`GoodA`).  `A₁` still satisfies
all of them (`goodA_A1`), so the family minimised over is still nonempty, and every later
use of the minimality of `A` (claims (3) and (9)) is unaffected.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Setup

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Bookkeeping about `wheelSystemA` -/

/-- A walk of `G|A` lifts to a walk of `G|B` whenever `A ⊆ B`. -/
private theorem reachable_induce_mono {G : SimpleGraph V} {A B : Set V} (hAB : A ⊆ B)
    {u v : V} (hu : u ∈ A) (hv : v ∈ A)
    (hr : (G.induce A).Reachable ⟨u, hu⟩ ⟨v, hv⟩) :
    (G.induce B).Reachable ⟨u, hAB hu⟩ ⟨v, hAB hv⟩ := by
  obtain ⟨p⟩ := hr
  exact ⟨SimpleGraph.Walk.map
    (⟨fun w => ⟨w.1, hAB w.2⟩, fun {_ _} h => h⟩ : (G.induce A) →g (G.induce B)) p⟩

/-- `X₁ = {x₀, x₁}`. -/
theorem wheelSystemX_one (x : ℕ → V) :
    wheelSystemX x 1 = ({x 0, x 1} : Set V) := by
  ext v
  simp only [wheelSystemX, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    interval_cases j
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨1, by omega, rfl⟩

/-- Membership in `Aᵢ` exhibits a member of the defining family. -/
theorem mem_wheelSystemA {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {i : ℕ} {v : V} (hv : v ∈ wheelSystemA G z A₀ x i) :
    ∃ A : Set V, (A₀ ⊆ A ∧ ConnectedSet G A ∧ (∀ w ∈ A, ¬ G.Adj z w) ∧
      (∀ w ∈ A, ¬ VertexComplete G w (wheelSystemX x i))) ∧ v ∈ A := hv

/-- Any member of the defining family of `Aᵢ` is contained in `Aᵢ`. -/
theorem subset_wheelSystemA {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {i : ℕ} {A : Set V} (hA : A₀ ⊆ A) (hAc : ConnectedSet G A)
    (hAz : ∀ w ∈ A, ¬ G.Adj z w)
    (hAX : ∀ w ∈ A, ¬ VertexComplete G w (wheelSystemX x i)) :
    A ⊆ wheelSystemA G z A₀ x i :=
  fun w hw => ⟨A, ⟨hA, hAc, hAz, hAX⟩, hw⟩

/-- `Aᵢ` contains no neighbour of `z`. -/
theorem wheelSystemA_no_z {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {i : ℕ} : ∀ v ∈ wheelSystemA G z A₀ x i, ¬ G.Adj z v := by
  intro v hv
  obtain ⟨A, ⟨-, -, hAz, -⟩, hvA⟩ := mem_wheelSystemA hv
  exact hAz v hvA

/-- `Aᵢ` contains no `Xᵢ`-complete vertex. -/
theorem wheelSystemA_no_complete {G : SimpleGraph V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {i : ℕ} :
    ∀ v ∈ wheelSystemA G z A₀ x i, ¬ VertexComplete G v (wheelSystemX x i) := by
  intro v hv
  obtain ⟨A, ⟨-, -, -, hAX⟩, hvA⟩ := mem_wheelSystemA hv
  exact hAX v hvA

/-- `A₀ ⊆ A₁`: the frame's own set belongs to the family defining `A₁`, because
condition 1 of a wheel system says that no vertex of `A₀` is `{x₀,x₁}`-complete. -/
theorem A0_subset_A1 {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {t : ℕ} (hframe : IsFrame G z A₀) (hws : IsWheelSystem G z A₀ x t) :
    A₀ ⊆ wheelSystemA G z A₀ x 1 := by
  refine subset_wheelSystemA Set.Subset.rfl hframe.2.1 hframe.2.2.2 ?_
  intro w hw
  rw [wheelSystemX_one]
  exact hws.2.2.2.1.2.2 w hw

/-- `A₁` is connected. -/
theorem A1_connected {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {t : ℕ} (hframe : IsFrame G z A₀) (hws : IsWheelSystem G z A₀ x t) :
    ConnectedSet G (wheelSystemA G z A₀ x 1) := by
  obtain ⟨a₀, ha₀⟩ := hframe.1
  have hsub : A₀ ⊆ wheelSystemA G z A₀ x 1 := A0_subset_A1 hframe hws
  have key : ∀ u : ↥(wheelSystemA G z A₀ x 1),
      (G.induce (wheelSystemA G z A₀ x 1)).Reachable u ⟨a₀, hsub ha₀⟩ := by
    rintro ⟨u, hu⟩
    obtain ⟨A, ⟨hA0, hAc, hAz, hAX⟩, huA⟩ := mem_wheelSystemA hu
    have hAsub : A ⊆ wheelSystemA G z A₀ x 1 := subset_wheelSystemA hA0 hAc hAz hAX
    have ha₀A : a₀ ∈ A := hA0 ha₀
    exact reachable_induce_mono hAsub huA ha₀A (hAc ⟨u, huA⟩ ⟨a₀, ha₀A⟩)
  intro u v
  exact (key u).trans (key v).symm

/-- `x₀` has a neighbour in `A₁` (it has one in `A₀`). -/
theorem x0_nb_A1 {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {t : ℕ} (hframe : IsFrame G z A₀) (hws : IsWheelSystem G z A₀ x t) :
    ∃ a ∈ wheelSystemA G z A₀ x 1, G.Adj (x 0) a := by
  obtain ⟨a, ha, hadj⟩ := hws.2.2.2.1.1
  exact ⟨a, A0_subset_A1 hframe hws ha, hadj⟩

/-- `x₁` has a neighbour in `A₁`. -/
theorem x1_nb_A1 {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {t : ℕ} (hframe : IsFrame G z A₀) (hws : IsWheelSystem G z A₀ x t) :
    ∃ a ∈ wheelSystemA G z A₀ x 1, G.Adj (x 1) a := by
  obtain ⟨a, ha, hadj⟩ := hws.2.2.2.1.2.1
  exact ⟨a, A0_subset_A1 hframe hws ha, hadj⟩

/-- `x₂` has a neighbour in `A₁`: this is exactly condition 2 of a wheel system
at `i = 2` ("condition 2 just says that `xᵢ` has a neighbour in `A_{i−1}`"). -/
theorem x2_nb_A1 {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    (hws : IsWheelSystem G z A₀ x 2) :
    ∃ a ∈ wheelSystemA G z A₀ x 1, G.Adj (x 2) a := by
  obtain ⟨B, hB0, hBc, ⟨b, hbB, hadj⟩, hBz, hBX⟩ := hws.2.2.2.2.1 2 (by omega) (by omega)
  refine ⟨b, subset_wheelSystemA hB0 hBc hBz ?_ hbB, hadj⟩
  simpa using hBX

/-- `x₀` and `x₁` are nonadjacent: condition 3 of a wheel system at `i = 1` says
that `x₁` is not `X₀ = {x₀}`-complete. -/
theorem x0_not_adj_x1 {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {t : ℕ} (hws : IsWheelSystem G z A₀ x t) : ¬ G.Adj (x 0) (x 1) := by
  intro hadj
  refine hws.2.2.2.2.2.1 1 (by omega) hws.1 ?_
  intro w hw
  obtain ⟨j, hj, rfl⟩ := hw
  interval_cases j
  exact hadj.symm

/-! ### The extremal choices of the printed proof -/

/-- The properties the printed proof requires of `A`:

* `A ⊆ A₁`;
* `A` is connected;
* `x₀, x₁, x₂` all have neighbours in `A`;
* every vertex in `Y` that is nonadjacent to `x₂` has a neighbour in `A`;
* **and** (see the module header) `y` has a neighbour in `A`. -/
def GoodA (G : SimpleGraph V) (z : V) (A₀ : Set V) (x : ℕ → V) (Y : Set V)
    (y : V) (A : Set V) : Prop :=
  A ⊆ wheelSystemA G z A₀ x 1 ∧ ConnectedSet G A ∧
    (∃ a ∈ A, G.Adj (x 0) a) ∧ (∃ a ∈ A, G.Adj (x 1) a) ∧ (∃ a ∈ A, G.Adj (x 2) a) ∧
    (∀ w ∈ Y, ¬ G.Adj w (x 2) → ∃ a ∈ A, G.Adj w a) ∧
    (∃ a ∈ A, G.Adj y a)

/-- The hypotheses that 19.2 places on `Y`. -/
def Hyp192 (G : SimpleGraph V) (z : V) (A₀ : Set V) (x : ℕ → V) (Y : Set V) : Prop :=
  (∀ y ∈ Y, y ≠ z ∧ y ≠ x 0 ∧ y ≠ x 1 ∧ y ≠ x 2) ∧
  AnticonnectedSet G Y ∧
  VertexComplete G (x 0) Y ∧ VertexComplete G (x 1) Y ∧ ¬ VertexComplete G (x 2) Y ∧
  (∀ y ∈ Y, ¬ G.Adj y (x 2) →
    (∃ a ∈ wheelSystemA G z A₀ x 1, G.Adj y a) ∧ G.Adj y z)

/-- The conclusion of 19.2. -/
def Concl192 (G : SimpleGraph V) (z : V) (A₀ : Set V) (x : ℕ → V) (Y : Set V) : Prop :=
  VertexComplete G z Y ∧
    ∃ C : List V, IsWheel G C Y ∧
      x 0 ∈ C ∧ x 1 ∈ C ∧ z ∈ C ∧
      {v : V | v ∈ C} ⊆ ({x 0, x 1, z} : Set V) ∪ wheelSystemA G z A₀ x 1

/-- The induction hypothesis carried by the printed proof of 19.2.

PAPER (printed p. 118): *"If possible, choose `Y` not satisfying the theorem, with
`|Y|` minimum."*

The counterexample minimised over is a whole tuple `(G, (z,A₀), x₀x₁x₂, Y)`, not just
the set `Y` inside one fixed graph: nothing in the printed proof keeps the graph fixed.
Claim (2) uses exactly that extra freedom.  It applies the theorem to the graph induced
on `A ∪ {x₀,x₁,x₂,z} ∪ Y₀` with the frame `(z,A)`, where the set called `A₁` is `A`
itself, and so obtains a wheel whose rim lies in `{x₀,x₁,z} ∪ A` rather than merely in
`{x₀,x₁,z} ∪ A₁`; see `Thm192Claim2Localization.inductive_wheel_with_rim_in_A`.

`IHInduced G n` is that half of the induction hypothesis: 19.2 holds in every induced
subgraph of `G`, for every frame and wheel system there, and every hub of size less
than `n`.  (The other half — 19.2 in `G` itself for hubs smaller than `Y` — is the
`∀ Y'` clause that accompanies it in every lemma of the proof.)  Only the vertex set
shrinks, so the recursion is on `n` alone; `Thm192Claim2Uniform.uniform_induction`
runs it. -/
def IHInduced (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ (S : Set V) (z' : ↥S) (A' : Set ↥S) (x' : ℕ → ↥S) (Y' : Set ↥S),
    InF7 (G.induce S) → IsFrame (G.induce S) z' A' →
    IsWheelSystem (G.induce S) z' A' x' 2 → Y'.ncard < n →
    Hyp192 (G.induce S) z' A' x' Y' → Concl192 (G.induce S) z' A' x' Y'

/-- `IHInduced` is antitone in the bound: an induction hypothesis for hubs smaller
than `n` is one for hubs smaller than any `m ≤ n`. -/
theorem IHInduced_mono {G : SimpleGraph V} {m n : ℕ} (hmn : m ≤ n)
    (h : IHInduced G n) : IHInduced G m :=
  fun S z' A' x' Y' hG hfr hws hlt => h S z' A' x' Y' hG hfr hws (lt_of_lt_of_le hlt hmn)

/-- `A₁` itself is a good `A`, so the family the paper minimises over is nonempty. -/
theorem goodA_A1 {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {Y : Set V}
    {y : V} (hframe : IsFrame G z A₀) (hws : IsWheelSystem G z A₀ x 2)
    (hHyp : Hyp192 G z A₀ x Y) (hy : ∃ a ∈ wheelSystemA G z A₀ x 1, G.Adj y a) :
    GoodA G z A₀ x Y y (wheelSystemA G z A₀ x 1) :=
  ⟨Set.Subset.rfl, A1_connected hframe hws, x0_nb_A1 hframe hws, x1_nb_A1 hframe hws,
    x2_nb_A1 hws, (fun w hw hnw => (hHyp.2.2.2.2.2 w hw hnw).1), hy⟩

/-- *"It follows from the hypotheses that `A, Y` are both nonempty."* — the `Y` half. -/
theorem Y_nonempty {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {Y : Set V}
    (hHyp : Hyp192 G z A₀ x Y) : Y.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  exact hHyp.2.2.2.2.1 (by rw [h]; intro w hw; exact absurd hw (Set.notMem_empty w))

/-- *"It follows from the hypotheses that `A, Y` are both nonempty."* — the `A` half. -/
theorem goodA_nonempty {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {Y : Set V} {y : V} {A : Set V} (hA : GoodA G z A₀ x Y y A) : A.Nonempty := by
  obtain ⟨a, ha, -⟩ := hA.2.2.1
  exact ⟨a, ha⟩

/-- Some vertex of `Y` is nonadjacent to `x₂` (that is what *"`x₂` is not
`Y`-complete"* says). -/
theorem exists_nonneighbour_x2 {G : SimpleGraph V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {Y : Set V} (hHyp : Hyp192 G z A₀ x Y) :
    ∃ y ∈ Y, ¬ G.Adj y (x 2) := by
  have h := hHyp.2.2.2.2.1
  simp only [VertexComplete, not_forall] at h
  obtain ⟨y, hy⟩ := h
  obtain ⟨hyY, hyadj⟩ := by simpa using hy
  exact ⟨y, hyY, fun hcon => hyadj hcon.symm⟩

/-- A wheel `(C, W)` whose rim lies in `{x₀,x₁,z} ∪ A₁` has a `W`-complete vertex
in `A₁`: the wheel supplies two *disjoint* `W`-complete edges of `C`, i.e. four
distinct `W`-complete vertices of the rim, and `{x₀,x₁,z}` has only three
elements. -/
theorem wheel_complete_vertex_in_A1 {G : SimpleGraph V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {W : Set V} {C : List V} (hW : IsWheel G C W)
    (hCsub : {v : V | v ∈ C} ⊆ ({x 0, x 1, z} : Set V) ∪ wheelSystemA G z A₀ x 1) :
    ∃ a ∈ wheelSystemA G z A₀ x 1, VertexComplete G a W := by
  obtain ⟨-, -, a, b, c, d, ha, hb, hc, hd, hab, hcd, hac, had, hbc, hbd⟩ := hW
  by_contra hcon
  push_neg at hcon
  have step : ∀ w : V, w ∈ C → VertexComplete G w W → w = x 0 ∨ w = x 1 ∨ w = z := by
    intro w hw hwW
    rcases hCsub hw with h | h
    · simpa using h
    · exact absurd hwW (hcon w h)
  have ha' := step a ha hab.2.1
  have hb' := step b hb hab.2.2
  have hc' := step c hc hcd.2.1
  have hd' := step d hd hcd.2.2
  have hab' : a ≠ b := hab.1.ne
  have hcd' : c ≠ d := hcd.1.ne
  rcases ha' with ha' | ha' | ha' <;> rcases hb' with hb' | hb' | hb' <;>
    rcases hc' with hc' | hc' | hc' <;> rcases hd' with hd' | hd' | hd' <;> simp_all

/-- *"For fixed `Y` choose `A ⊆ A₁` minimal with the properties that …"* — the second
extremal choice of the printed proof, taken (see the module header) *after* claim (1)
and with the extra clause *"`y` has a neighbour in `A`"*. -/
theorem exists_minimal_goodA {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {Y : Set V} {y : V} (hframe : IsFrame G z A₀) (hws : IsWheelSystem G z A₀ x 2)
    (hHyp : Hyp192 G z A₀ x Y) (hy : ∃ a ∈ wheelSystemA G z A₀ x 1, G.Adj y a) :
    ∃ A : Set V, GoodA G z A₀ x Y y A ∧
      ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard := by
  obtain ⟨A, hA, hAmin⟩ :
      ∃ A ∈ {B : Set V | GoodA G z A₀ x Y y B},
        ∀ B ∈ {B : Set V | GoodA G z A₀ x Y y B}, A.ncard ≤ B.ncard :=
    Set.exists_min_image _ Set.ncard (Set.toFinite _)
      ⟨wheelSystemA G z A₀ x 1, goodA_A1 hframe hws hHyp hy⟩
  exact ⟨A, hA, hAmin⟩

/-- *"If possible, choose `Y` not satisfying the theorem, with `|Y|` minimum."* — the
first extremal choice of the printed proof, in the form of a strong induction on
`|Y|`.  The `zero` case is vacuous because `Y` is nonempty (`Y_nonempty`). -/
theorem aux {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    (step : ∀ Y : Set V, Hyp192 G z A₀ x Y →
      (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') →
      Concl192 G z A₀ x Y) :
    ∀ Y : Set V, Hyp192 G z A₀ x Y → Concl192 G z A₀ x Y := by
  have main : ∀ n : ℕ, ∀ Y : Set V, Y.ncard ≤ n →
      Hyp192 G z A₀ x Y → Concl192 G z A₀ x Y := by
    intro n
    induction n with
    | zero =>
        intro Y hcard hHyp
        exfalso
        have hYe : Y = ∅ := (Set.ncard_eq_zero (Set.toFinite Y)).mp (Nat.le_zero.mp hcard)
        exact absurd hYe (Set.nonempty_iff_ne_empty.mp (Y_nonempty hHyp))
    | succ n ihn =>
        intro Y hcard hHyp
        exact step Y hHyp (fun Y' hlt hHyp' => ihn Y' (by omega) hHyp')
  exact fun Y hHyp => main Y.ncard Y le_rfl hHyp

end Workspace.ProofLemmas.Thm192Setup
