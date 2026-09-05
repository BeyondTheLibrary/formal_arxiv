import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm224ClaimsDefs
import Workspace.ProofLemmas.Thm224Claim6LongAntipathEven
import Workspace.ProofLemmas.Thm224Claim6OddAntipathForcesZConflict

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm224Claim6

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm224Claims

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **(6)** *"If `x_{t+1}` is adjacent to `u₁` then `u₁` is `X_t`-complete."* -/
theorem claim6 {G : SimpleGraph V} (hG : InF8 G) {C : List V} {Y : Set V}
    (hopt : OptimalWheel G C Y) {z : V} {x : ℕ → V} {T : List V}
    (hT : IsTail G C Y z (x 0) (x 1) T) {y : V} {R : List V} (hTshape : T = z :: y :: R)
    {A₀ : Set V} (hA₀ : A₀ = {v : V | v ∈ C} \ {z, x 0, x 1}) {t : ℕ}
    (hhub : IsHubForWheelSystem G z A₀ x (t + 1) (Y ∪ {y}))
    (hcon : VertexAnticomplete G y (wheelSystemA G z A₀ x t ∪ {x (t + 1)}))
    {u : List V} (hu : IsUPath G z A₀ x t Y T y u) (hlen : Even u.length) :
    ∀ u₁ ∈ u.head?, G.Adj (x (t + 1)) u₁ → VertexComplete G u₁ (wheelSystemX x t) := by
  classical
  intro u₁ hu₁ hqu₁
  rcases u with _ | ⟨v, vs⟩
  · simp at hu₁
  · simp only [List.head?_cons, Option.mem_some_iff] at hu₁
    subst v
    rcases vs with _ | ⟨u₂, r⟩
    · have he := Nat.even_iff.mp hlen
      simp at he
    · by_contra hu₁notX
      obtain ⟨L, hL, hLint, hext, _hlarge, heven, havoid⟩ :=
        Workspace.ProofLemmas.Thm224Claim6LongAntipathEven.thm224Claim6LongAntipathEven
          hG hopt hT hTshape hA₀ hhub hcon hu hlen rfl hqu₁ hu₁notX
      exact
        Workspace.ProofLemmas.Thm224Claim6OddAntipathForcesZConflict.thm224Claim6OddAntipathForcesZConflict
          hG hopt hT hTshape hA₀ hhub hcon hu hlen rfl hL hLint hext heven havoid

end Workspace.ProofLemmas.Thm224Claim6
