import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.Thm224Claims

set_option autoImplicit false

namespace Workspace.Statements.S22

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

open Workspace.ProofLemmas.Thm224Claims

/-- **22.4** — the paper's proof.  *"We assume for a contradiction that `y` has no neighbour in
`A_t ∪ {x_{t+1}}`.  Let `y-u₁-⋯-uₙ` be a minimal subpath of `T \ z` such that `uₙ` has a neighbour
in `A_t` …"*, then claims (1)–(7) and the final 2.10 / 17.1 paragraph.  The claims live in
`Workspace.ProofLemmas.Thm224Claims`; this is the assembly. -/
theorem thm_22_4 (G : SimpleGraph V) (hG : InF8 G)
    (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y)
    (hnokite : ¬ ∃ v : V, IsKite G C Y v)
    (z : V) (x : ℕ → V) (T : List V) (hT : IsTail G C Y z (x 0) (x 1) T)
    (y : V) (R : List V) (hTshape : T = z :: y :: R)
    (A₀ : Set V) (hA₀ : A₀ = {v : V | v ∈ C} \ {z, x 0, x 1})
    (t : ℕ) (hhub : IsHubForWheelSystem G z A₀ x (t + 1) (Y ∪ {y})) :
    ∃ a ∈ (wheelSystemA G z A₀ x t ∪ {x (t + 1)} : Set V), G.Adj y a := by
  -- *"We assume for a contradiction that `y` has no neighbour in `A_t ∪ {x_{t+1}}`."*
  by_contra hcon0
  push_neg at hcon0
  have hcon : VertexAnticomplete G y (wheelSystemA G z A₀ x t ∪ {x (t + 1)}) := hcon0
  -- *"Let `y-u₁-⋯-uₙ` be a minimal subpath of `T \ z` such that `uₙ` has a neighbour in `A_t`."*
  obtain ⟨u, hu⟩ := exists_uPath hG hopt hT hTshape hA₀ hhub hcon
  -- (2) *"… and so `n` is even."*
  have hlen : Even u.length :=
    uPath_length_even hG hopt hnokite hT hTshape hA₀ hhub hcon hu
  -- (3) *"`x_{t+1}` is adjacent to one of `u₁,…,u_{n−1}`."*
  have hadj : ∃ v ∈ u.dropLast, G.Adj (x (t + 1)) v :=
    xt1_adj_dropLast hG hopt hnokite hT hTshape hA₀ hhub hcon hu hlen
  -- (7) *"None of `u₁,…,u_{n−1}` is `X_t`-complete."*
  have hXt : ∀ v ∈ u.dropLast, ¬ VertexComplete G v (wheelSystemX x t) :=
    no_dropLast_Xt_complete hG hopt hnokite hT hTshape hA₀ hhub hcon hu hlen
  -- the final paragraph: 2.10 gives a leap or a hat; the leap contradicts 13.6 and the hat
  -- contradicts 17.1.
  exact endgame hG hopt hnokite hT hTshape hA₀ hhub hcon hu hlen hadj hXt


end SPGT

end Workspace.Statements.S22
