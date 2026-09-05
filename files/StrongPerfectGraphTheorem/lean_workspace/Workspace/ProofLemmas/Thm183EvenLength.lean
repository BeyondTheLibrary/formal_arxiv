import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.Statements.S13.Thm_13_6
import Workspace.ProofLemmas.PathBasics

/-!
# 18.3, first conclusion: *"Then `P` has even length."*

The opening sentence of the printed proof of **18.3** (`paper/proofs/18_3.md`, published page
110) is a complete argument on its own:

> *"Since `P` is a path of length ≥ 4, and its ends are `X`-complete and its internal vertices
> are not, it follows that `P` has even length, by 13.6."*

This module is that sentence and nothing else.  It is stated for `G ∈ F₅` (13.6's hypothesis)
rather than `G ∈ F₇`; the caller supplies `hG.1.1 : InF5 G` from `hG : InF7 G`.

**How the citation of 13.6 discharges it.**  13.6 says that an *odd* path whose two ends are
`X`-complete, with `X` anticonnected and disjoint from `V(P)`, either has an `X`-complete edge
or has length exactly `3`.  Suppose `P` were odd.

* An `X`-complete edge `uv` of `P` has both ends `X`-complete, so by the uniqueness hypothesis
  each of `u, v` is `p₁` or `pₙ`; `u ≠ v` because they are adjacent, so `p₁pₙ` would be an edge
  — impossible, since `P` is an induced path with `n ≥ 5` vertices.
* Length `3` contradicts `n ≥ 5`, i.e. length `≥ 4`.

So `P` is even.

Note that no part of the paper's *second* or *third* conclusion is used or proved here; see
`lean_workspace/ProofAttempts/thm_18_3/Claim2_Refutation.lean` for the defect in the frozen
form of the second conclusion.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm183EvenLength

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **18.3, first conclusion.**  *"Since `P` is a path of length ≥ 4, and its ends are
`X`-complete and its internal vertices are not, it follows that `P` has even length, by 13.6."*

`hXuniq` is 18.3's hypothesis *"`p₁, pₙ` are the only `X`-complete vertices of `P`"*, and
`hpX` is the half of *"`P` is a path of `G \ (X ∪ Y)`"* that this argument needs. -/
theorem even_pathLength_of_ends_only_XComplete
    (G : SimpleGraph V) (hG5 : InF5 G) (X : Set V) (hXa : AnticonnectedSet G X)
    (p : List V) (p₁ pₙ : V) (hp : IsPathList G p)
    (hpX : ∀ w ∈ p, w ∉ X) (hn : 5 ≤ p.length)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pₙ)
    (hXuniq : ∀ w ∈ p, (VertexComplete G w X ↔ (w = p₁ ∨ w = pₙ))) :
    Even (pathLength p) := by
  rcases Nat.even_or_odd (pathLength p) with hev | hodd
  · exact hev
  exfalso
  -- `P` has length `n - 1 ≥ 4`.
  have hplen : pathLength p = p.length - 1 := PathBasics.pathLength_eq p
  have h0lt : 0 < p.length := by omega
  have hnlt : p.length - 1 < p.length := by omega
  have hp0 : p[0]'h0lt = p₁ := PathBasics.getElem_zero_of_head? hhead h0lt
  have hpe : p[p.length - 1]'hnlt = pₙ := PathBasics.getElem_last_of_getLast? hlast h0lt
  -- The two ends of an induced path with `≥ 3` vertices are non-adjacent.
  have hnotadj : ¬ G.Adj p₁ pₙ := by
    rw [← hp0, ← hpe]; exact PathBasics.path_ends_not_adj hp (by omega)
  -- `X` is disjoint from `V(P)`: 13.6's hypothesis `X ⊆ V(G) \ V(P)`.
  have hXP : X ⊆ {v : V | v ∈ p}ᶜ := fun x hx hxp => hpX x hxp hx
  have hp₁mem : p₁ ∈ p := PathBasics.head_mem hhead
  have hpnmem : pₙ ∈ p := PathBasics.getLast_mem hlast
  have hc1 : VertexComplete G p₁ X := (hXuniq p₁ hp₁mem).mpr (Or.inl rfl)
  have hc2 : VertexComplete G pₙ X := (hXuniq pₙ hpnmem).mpr (Or.inr rfl)
  -- *"by 13.6"*
  rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG5 p p₁ pₙ ⟨hp, hhead, hlast⟩ hodd
      X hXP hXa hc1 hc2 with hedge | hthree
  · -- 13.6(1): an `X`-complete edge of `P`.  Both its ends are `X`-complete, hence each is
    -- `p₁` or `pₙ`, so `p₁pₙ` would be an edge of `G`.
    obtain ⟨u, hu, v, hv, hadj, hcu, hcv⟩ := hedge
    rcases (hXuniq u hu).mp hcu with rfl | rfl <;>
      rcases (hXuniq v hv).mp hcv with rfl | rfl
    · exact G.irrefl hadj
    · exact hnotadj hadj
    · exact hnotadj hadj.symm
    · exact G.irrefl hadj
  · -- 13.6(2): `P` would have length `3`, but it has length `≥ 4`.
    obtain ⟨h3, -⟩ := hthree
    omega

end Workspace.ProofLemmas.Thm183EvenLength
