/-  Proof attempt for statement 20.1 of Chudnovsky-Robertson-Seymour-Thomas,
    *The Strong Perfect Graph Theorem*.  Reproduces the printed proof
    "Proof of 20.1, assuming 20.2, 20.3, 20.4, and 20.5" (printed p. 126)
    step for step: induction on the height `t`, base case `t = 3` by 20.2,
    inductive step via 20.3 / 20.4 and — in the polished case — 20.5.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Statements.S20.Thm_20_2
import Workspace.Statements.S20.Thm_20_3
import Workspace.Statements.S20.Thm_20_4
import Workspace.Statements.S20.Thm_20_5
import Workspace.ProofLemmas.Thm201HubBasics

/-!
# Section 20 — Diamond and square wheel systems

The five numbered statements 20.1 … 20.5 of Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem* (published/*Annals* version, printed pages
123–130).  Source of the verbatim quotations:
`paper/pdf/S20_Diamond_and_square_wheel_systems.md`, `## Numbered statements`.

Every defined term used here already lives in an imported module; nothing is
restated:

* `Workspace.Types.Core` — `VertexComplete`, `AnticonnectedSet`;
* `Workspace.Types.Wheels` — `IsWheel` (§16's *wheel* `(C,Y)`);
* `Workspace.Types.WheelSystems` — `IsFrame`, `IsYDiamond`, `IsYSquare`,
  `IsPolishedYDiamond` (§20's three special kinds of wheel system, each of which
  already contains the common preamble: `x₀,…,x_t` is a wheel system, `Y` is
  nonempty and anticonnected and disjoint from `{z,x₀,…,x_t}`, `x₀,…,x_{t−1}` are
  `Y`-complete and `x_t` is not);
* `Workspace.Types.Classes` — `InF7` (the class `F₇` of §1).

Encoding conventions (see `paper/spec/CONVENTIONS.md`):

* a **wheel system** `x₀,…,x_t` is the pair of a sequence `x : ℕ → V` and its
  *height* `t : ℕ`; only `x 0, …, x t` are constrained;
* *"there is a `Y`-diamond in `G` of height `n`"* is
  `∃ x : ℕ → V, IsYDiamond G z A₀ x n Y`, and similarly for squares and polished
  diamonds — the frame `(z,A₀)` is the fixed one of Section 19, which the paper
  leaves implicit;
* *"`Y ⊆ V(G) \ (A₀ ∪ {z})`"* is `∀ y ∈ Y, y ∉ A₀ ∧ y ≠ z`, the same rendering
  used by `IsHubForWheelSystem`;
* *"`G` contains a wheel with hub `Y`"* / *"`G` contains a wheel `(C,Y)`"* are
  both `∃ C : List V, IsWheel G C Y`;
* natural subtraction is used for the paper's `t − 1`, which is harmless because
  every occurrence is guarded by `t ≥ 4` (20.3, 20.4) or `t + 1 ≥ 5` (20.5).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.Statements.S20

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

open Workspace.ProofLemmas.Thm201HubBasics in
/-- The hub of a `Y`-diamond automatically avoids `A₀ ∪ {z}`.

This is the side condition that the printed proof of 20.1 tacitly assumes when
it feeds the set `Y'` produced by 20.3 back into the induction: 20.3 delivers an
anticonnected `Y'` with `Y ⊆ Y'` but says nothing about `Y' ∩ (A₀ ∪ {z})`.  It
is free: `x₀, x₁` are `Y'`-complete, so every `y ∈ Y'` is `{x₀,x₁}`-complete,
while a frame vertex `a ∈ A₀` never is. -/
private theorem hubsub_of_diamond {G : SimpleGraph V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} {Y : Set V} (h : IsYDiamond G z A₀ x t Y) :
    ∀ y ∈ Y, y ∉ A₀ ∧ y ≠ z := by
  obtain ⟨hws, -, -, ⟨hzY, -⟩, hcomp, -, ht3, -⟩ := h
  exact hub_avoids_frame_of_wheelSystem hws (by omega) hzY hcomp

open Workspace.ProofLemmas.Thm201HubBasics in
/-- The same fact for a `Y`-square. -/
private theorem hubsub_of_square {G : SimpleGraph V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} {Y : Set V} (h : IsYSquare G z A₀ x t Y) :
    ∀ y ∈ Y, y ∉ A₀ ∧ y ≠ z := by
  obtain ⟨hws, -, -, ⟨hzY, -⟩, hcomp, -, ht3, -⟩ := h
  exact hub_avoids_frame_of_wheelSystem hws (by omega) hzY hcomp

/-- **20.1** (printed p. 123).

PAPER: *"Let `G ∈ F₇` and let `(z,A₀)` be a frame.  For all
`Y ⊆ V(G) \ (A₀ ∪ {z})`, if `Y` is nonempty and anticonnected, and there is either
a `Y`-diamond or a `Y`-square in `G`, then `z` is `Y`-complete and `G` contains a
wheel with hub `Y`."*

Encoding notes.

* The paper's *"For all `Y ⊆ …`"* is the universal quantifier over `Y` carried by
  the theorem's binder.
* *"there is either a `Y`-diamond or a `Y`-square in `G`"* leaves the height of
  the diamond/square existentially quantified (both notions already require
  `t ≥ 3` internally), and the two alternatives are kept in the printed order.
* The published statement says *"a wheel with hub `Y`"* where the draft said
  *"a wheel `(C,Y)`"*; these are the same thing, the hub of `(C,Y)` being `Y`. -/
theorem thm_20_1 (G : SimpleGraph V) (hG : InF7 G)
    (z : V) (A₀ : Set V) (hframe : IsFrame G z A₀)
    (Y : Set V) (hYsub : ∀ y ∈ Y, y ∉ A₀ ∧ y ≠ z)
    (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (hDS : (∃ (x : ℕ → V) (t : ℕ), IsYDiamond G z A₀ x t Y) ∨
      (∃ (x : ℕ → V) (t : ℕ), IsYSquare G z A₀ x t Y)) :
    VertexComplete G z Y ∧ ∃ C : List V, IsWheel G C Y := by
  -- PAPER: "We shall prove by induction on `t` that for any nonempty anticonnected
  -- `Y ⊆ V(G) \ (A₀ ∪ {z})`, if there is a `Y`-diamond or `Y`-square in `G` of
  -- height `t`, then `z` is `Y`-complete and `G` contains a wheel with hub `Y`."
  suffices key : ∀ t : ℕ, ∀ W : Set V, W.Nonempty → AnticonnectedSet G W →
      (∀ y ∈ W, y ∉ A₀ ∧ y ≠ z) →
      ((∃ x : ℕ → V, IsYDiamond G z A₀ x t W) ∨
        (∃ x : ℕ → V, IsYSquare G z A₀ x t W)) →
      VertexComplete G z W ∧ ∃ C : List V, IsWheel G C W by
    rcases hDS with ⟨x, t, hd⟩ | ⟨x, t, hs⟩
    · exact key t Y hYne hYanti hYsub (Or.inl ⟨x, hd⟩)
    · exact key t Y hYne hYanti hYsub (Or.inr ⟨x, hs⟩)
  intro t
  induction t using Nat.strong_induction_on with
  | _ t IH =>
  intro W hWne hWanti hWsub hW
  -- PAPER: "Certainly `t ≥ 3`" — this is part of the definition of a diamond/square.
  have ht3 : 3 ≤ t := by
    rcases hW with ⟨x, hd⟩ | ⟨x, hs⟩
    · obtain ⟨-, -, -, -, -, -, ht, -⟩ := hd; exact ht
    · obtain ⟨-, -, -, -, -, -, ht, -⟩ := hs; exact ht
  rcases eq_or_lt_of_le ht3 with ht | ht4
  · -- PAPER: "if `t = 3` then the result holds by 20.2".
    subst ht
    have h202 := thm_20_2 G hG z A₀ hframe W hWsub hWne hWanti
    rcases hW with ⟨x, hd⟩ | ⟨x, hs⟩
    · -- 20.2 produces a wheel with the *larger* hub `W ∪ {x₃}`; the paper's own
      -- remark ("annoying wastage") is that only a wheel with hub `W` is needed.
      obtain ⟨hzc, C, hwheel⟩ := h202.2.2 x hd
      exact ⟨hzc, C, Workspace.ProofLemmas.Thm201HubBasics.wheel_hub_mono
        Set.subset_union_left hWne hWanti hwheel⟩
    · -- 20.2: there is no `W`-square of height 3.
      exact absurd ⟨x, hs⟩ h202.1
  · -- PAPER: "so we may assume that `t ≥ 4`."
    have ht : 4 ≤ t := ht4
    -- PAPER: "By 20.3 and 20.4, we may assume that there is an anticonnected set
    -- `Y'` with `Y' ⊆ V(G) \ (A₀ ∪ {z})` such that either `Y ⊆ Y'` or `z` is not
    -- `Y'`-complete, and such that either: [diamond of height t−1] or
    -- [square of height t−1] or [polished diamond of height t]."
    have step : (VertexComplete G z W ∧ ∃ C : List V, IsWheel G C W) ∨
        ∃ Y' : Set V, Y'.Nonempty ∧ AnticonnectedSet G Y' ∧
          (∀ y ∈ Y', y ∉ A₀ ∧ y ≠ z) ∧
          (W ⊆ Y' ∨ ¬ VertexComplete G z Y') ∧
          ((∃ x' : ℕ → V, IsYDiamond G z A₀ x' (t - 1) Y') ∨
           (∃ x' : ℕ → V, IsYSquare G z A₀ x' (t - 1) Y') ∨
           (∃ x' : ℕ → V, IsPolishedYDiamond G z A₀ x' t Y')) := by
      rcases hW with ⟨x, hd⟩ | ⟨x, hs⟩
      · -- diamond of height `t ≥ 4`: this is 20.3, used contrapositively.
        by_cases hnone : ∃ Y' : Set V, AnticonnectedSet G Y' ∧ W ⊆ Y' ∧
            ((∃ x' : ℕ → V, IsYDiamond G z A₀ x' (t - 1) Y') ∨
             (∃ x' : ℕ → V, IsYSquare G z A₀ x' (t - 1) Y') ∨
             (∃ x' : ℕ → V, IsPolishedYDiamond G z A₀ x' t Y'))
        · obtain ⟨Y', hanti', hsub', halt⟩ := hnone
          refine Or.inr ⟨Y', hWne.mono hsub', hanti', ?_, Or.inl hsub', halt⟩
          rcases halt with ⟨x', hd'⟩ | ⟨x', hs'⟩ | ⟨x', hp'⟩
          · exact hubsub_of_diamond hd'
          · exact hubsub_of_square hs'
          · exact hubsub_of_diamond hp'.1
        · exact Or.inl (thm_20_3 G hG z A₀ hframe W hWsub hWne hWanti x t hd ht hnone)
      · -- square of height `t ≥ 4`: this is 20.4, applied directly.
        obtain ⟨Y', hne', hanti', hsub', hdisj', halt⟩ :=
          thm_20_4 G hG z A₀ hframe W hWsub hWne hWanti x t hs ht
        exact Or.inr ⟨Y', hne', hanti', hsub',
          hdisj'.imp (fun h => h.subset) id, halt⟩
    rcases step with hdone | ⟨Y', hne', hanti', hsub', hdisj', halt⟩
    · exact hdone
    -- The two "easy" cases of the trichotomy.
    have easy : ∀ s, s < t → ∀ Y'' : Set V, Y''.Nonempty → AnticonnectedSet G Y'' →
        (∀ y ∈ Y'', y ∉ A₀ ∧ y ≠ z) →
        ((∃ x' : ℕ → V, IsYDiamond G z A₀ x' s Y'') ∨
          (∃ x' : ℕ → V, IsYSquare G z A₀ x' s Y'')) →
        VertexComplete G z Y'' ∧ ∃ C : List V, IsWheel G C Y'' := fun s hs => IH s hs
    -- In every branch below we end up with `z` being `Y'`-complete together with a
    -- wheel whose hub contains `Y'`; that is exactly what the paper needs.
    suffices hstep : ∃ Y'' : Set V, Y' ⊆ Y'' ∧ VertexComplete G z Y'' ∧
        ∃ C : List V, IsWheel G C Y'' by
      obtain ⟨Y'', hY'Y'', hzc'', C, hwheel⟩ := hstep
      -- PAPER: "Since `z` is `Y'`-complete, it follows that `Y ⊆ Y'`, and so `z` is
      -- `Y`-complete and there is a wheel with hub `Y`, as required."
      have hzc' : VertexComplete G z Y' :=
        Workspace.ProofLemmas.Thm201HubBasics.vertexComplete_mono hY'Y'' hzc''
      have hWY' : W ⊆ Y' := hdisj'.resolve_right (fun hcon => hcon hzc')
      refine ⟨Workspace.ProofLemmas.Thm201HubBasics.vertexComplete_mono hWY' hzc', C, ?_⟩
      exact Workspace.ProofLemmas.Thm201HubBasics.wheel_hub_mono
        (hWY'.trans hY'Y'') hWne hWanti hwheel
    rcases halt with ⟨x', hd'⟩ | ⟨x', hs'⟩ | ⟨x', hp'⟩
    · -- PAPER, first case: "it follows from the inductive hypothesis that `z` is
      -- `Y'`-complete, and there is a wheel with hub `Y'`."
      obtain ⟨hzc', C, hwheel⟩ :=
        easy (t - 1) (by omega) Y' hne' hanti' hsub' (Or.inl ⟨x', hd'⟩)
      exact ⟨Y', subset_rfl, hzc', C, hwheel⟩
    · -- PAPER, second case: identical, with a square in place of a diamond.
      obtain ⟨hzc', C, hwheel⟩ :=
        easy (t - 1) (by omega) Y' hne' hanti' hsub' (Or.inr ⟨x', hs'⟩)
      exact ⟨Y', subset_rfl, hzc', C, hwheel⟩
    · -- PAPER: "Thus we may assume that the third case holds.  By 20.2 it follows
      -- that `t ≥ 5`".
      have ht5 : 5 ≤ t := by
        by_contra hcon
        have ht4' : t = 4 := by omega
        exact (thm_20_2 G hG z A₀ hframe Y' hsub' hne' hanti').2.1 ⟨x', ht4' ▸ hp'⟩
      -- PAPER: "and by 20.5, there is an anticonnected set `Y''` with
      -- `Y'' ⊆ V(G) \ (A₀ ∪ {z})` such that either `Y' ⊆ Y''` or `z` is not
      -- `Y''`-complete, and either: [diamond of height t−2] or [square of height
      -- t−2] or [polished diamond of height t−1]."
      have hp2 : IsPolishedYDiamond G z A₀ x' (t - 1 + 1) Y' := by
        have : t - 1 + 1 = t := by omega
        rw [this]; exact hp'
      obtain ⟨Y'', hne'', hanti'', hsub'', hdisj'', halt''⟩ :=
        thm_20_5 G hG z A₀ hframe Y' hsub' hne' hanti' x' (t - 1) hp2 (by omega)
      -- PAPER: "In each case it follows from the inductive hypothesis that `z` is
      -- `Y''`-complete and there is a wheel with hub `Y''`."
      have hgot : VertexComplete G z Y'' ∧ ∃ C : List V, IsWheel G C Y'' := by
        rcases halt'' with ⟨x'', hd''⟩ | ⟨x'', hs''⟩ | ⟨x'', hp''⟩
        · exact easy (t - 1 - 1) (by omega) Y'' hne'' hanti'' hsub'' (Or.inl ⟨x'', hd''⟩)
        · exact easy (t - 1 - 1) (by omega) Y'' hne'' hanti'' hsub'' (Or.inr ⟨x'', hs''⟩)
        · exact easy (t - 1) (by omega) Y'' hne'' hanti'' hsub'' (Or.inl ⟨x'', hp''.1⟩)
      obtain ⟨hzc'', C, hwheel⟩ := hgot
      -- PAPER: "Consequently `Y' ⊆ Y''`, and so `z` is `Y'`-complete".
      have hY'Y'' : Y' ⊆ Y'' := hdisj''.resolve_right (fun hcon => hcon hzc'')
      exact ⟨Y'', hY'Y'', hzc'', C, hwheel⟩


end SPGT

end Workspace.Statements.S20
