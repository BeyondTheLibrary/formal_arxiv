import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Pseudowheels
import Workspace.Types.Classes

/-!
# 18.6 — the shared vocabulary of the printed proof

The printed proof of **18.6** (`paper/proofs/18_6.md`, published page 114) opens

> *"Proof.  Suppose the theorem is false, and choose a minimal counterexample `F`.  From 18.5
> `|F| ≥ 2`."*

and then runs two numbered claims (1), (2) and a closing paragraph.  Every one of those steps
talks about *the same* three notions, so they are named once, here:

* `Adm G X Y P F` — the standing hypothesis on `F` in the statement of 18.6:
  *"Let `F ⊆ V(G) \ (X ∪ Y ∪ V(P))` be connected, such that no vertex in `F` is
  `Y`-complete."*
* `Good G X Y P p₁ pₙ F` — the *conclusion* of 18.6 for that particular `F`:
  *"Then there is a subpath `P'` of `P` such that …"*, verbatim in the shape of the frozen
  `Workspace.Statements.S18.SPGT.thm_18_6`.  A **counterexample** is an `F` with `Adm` and
  `¬ Good`.
* `MinCounterexample` — *"choose a minimal counterexample `F`"*.  Minimal in `|F|`: every
  admissible set strictly smaller than `F` is good.  This is exactly the form the printed proof
  uses it in ("*From the minimality of `F` …*", four times).

Nothing here corresponds to a numbered result of the paper; it is the proof's own vocabulary.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm186Setup

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Pseudowheels Workspace.Types.Pseudowheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER: *"Let `F ⊆ V(G) \ (X ∪ Y ∪ V(P))` be connected, such that no vertex in `F` is
`Y`-complete."* -/
def Adm (G : SimpleGraph V) (X Y : Set V) (P : List V) (F : Set V) : Prop :=
  (∀ f ∈ F, f ∉ X ∪ Y ∧ f ∉ P) ∧ ConnectedSet G F ∧ (∀ f ∈ F, ¬ VertexComplete G f Y)

/-- PAPER: *"Then there is a subpath `P'` of `P` such that `V(P')` contains all the attachments
of `F` in `P`; there is no `Y`-complete vertex in the interior of `P'`; and if some vertex of
`F` is `X`-complete then either `V(P') = {p₁}` or `pₙ ∈ V(P')`."*

Byte-for-byte the conclusion of the frozen `Workspace.Statements.S18.SPGT.thm_18_6`. -/
def Good (G : SimpleGraph V) (X Y : Set V) (P : List V) (p₁ pₙ : V) (F : Set V) : Prop :=
  ∃ q : List V, IsPathList G q ∧ q <:+: P ∧
    (∀ w ∈ attachments G F {w : V | w ∈ P}, w ∈ q) ∧
    (∀ w ∈ SPGT.interior q, ¬ VertexComplete G w Y) ∧
    ((∃ f ∈ F, VertexComplete G f X) → ({w : V | w ∈ q} = {p₁} ∨ pₙ ∈ q))

/-- PAPER: *"Suppose the theorem is false, and choose a minimal counterexample `F`."*

Minimality is in `|F|`, which is how the printed proof uses it: the sets `F \ {f₁}`,
`F \ {f_k}` and the various `{f_i, …, f_k}` it forms are all *smaller*, hence good. -/
def MinCounterexample (G : SimpleGraph V) (X Y : Set V) (P : List V) (p₁ pₙ : V)
    (F : Set V) : Prop :=
  Adm G X Y P F ∧ ¬ Good G X Y P p₁ pₙ F ∧
    ∀ F' : Set V, Adm G X Y P F' → F'.ncard < F.ncard → Good G X Y P p₁ pₙ F'

/-- *"Suppose the theorem is false, and choose a minimal counterexample `F`."*  A counterexample
of least cardinality exists as soon as there is one at all. -/
theorem exists_minCounterexample (G : SimpleGraph V) (X Y : Set V) (P : List V) (p₁ pₙ : V)
    (F : Set V) (hF : Adm G X Y P F) (hne : ¬ Good G X Y P p₁ pₙ F) :
    ∃ F₀ : Set V, MinCounterexample G X Y P p₁ pₙ F₀ := by
  classical
  have hex : ∃ n : ℕ, ∃ F' : Set V,
      Adm G X Y P F' ∧ ¬ Good G X Y P p₁ pₙ F' ∧ F'.ncard = n := ⟨F.ncard, F, hF, hne, rfl⟩
  obtain ⟨F₀, hadm, hng, hcard⟩ := Nat.find_spec hex
  refine ⟨F₀, hadm, hng, ?_⟩
  intro F' hF' hlt
  by_contra hg
  exact Nat.find_min hex (m := F'.ncard) (by omega) ⟨F', hF', hg, rfl⟩

end Workspace.ProofLemmas.Thm186Setup
