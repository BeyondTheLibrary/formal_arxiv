import Workspace.ProofLemmas.PseudowheelBuilder
import Workspace.ProofLemmas.Thm183EvenLength
import Workspace.ProofLemmas.Thm232Claim5SecondOutcome
import Workspace.Statements.S02.Thm_2_11

/-!
# Claim 23.2(5) once its path has been chosen

The absence of a pseudowheel identifies the vertices complete to the rim
pair. The path is even by 13.6. Each outcome of 2.11 then gives a member of
the pair with no neighbour in the path interior.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm232Claim5FromPath

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.PathBasics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (23.2(5), printed p. 141): "Since `G ∈ F₈`,
`(Y,{x₀,x₁},z-y-p₁-...-p_k)` is not a pseudowheel. ... So no other vertices
of the path are `{x₀,x₁}`-complete. By 2.11 ... one of `x₀,x₁` is
nonadjacent to all of `y,p₁,...,p_{k-1}`."

The set `X` stands for the rim pair. The proof works for any nonempty
anticonnected set `X` with the listed completeness properties. -/
theorem exists_anticomplete_interior (G : SimpleGraph V) (hG : InF8 G)
    (X Y : Set V) (hXY : Disjoint X Y) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXa : AnticonnectedSet G X) (hYa : AnticonnectedSet G Y)
    (hcompl : Complete G X Y) (P : List V) (z y pn : V)
    (hP : IsPathFrom G P z pn) (hsecond : P.tail.head? = some y)
    (hout : ∀ v ∈ P, v ∉ X ∧ v ∉ Y) (hlong : 4 ≤ pathLength P)
    (hYuniq : ∀ v ∈ P, VertexComplete G v Y ↔ v = z ∨ v = pn)
    (hzX : VertexComplete G z X) (hyX : ¬ VertexComplete G y X)
    (hpnX : ¬ VertexComplete G pn X) :
    ∃ a ∈ X, VertexAnticomplete G a {v : V | v ∈ SPGT.interior P} := by
  have hlen : 5 ≤ P.length := by unfold pathLength at hlong; omega
  have hYX : Complete G Y X := fun a ha b hb => (hcompl b hb a ha).symm
  have hXuniq := PseudowheelBuilder.unique_vertexComplete_of_no_pseudowheel
    hG.2.1 hXY.symm hYne hXne hYa hXa hYX hP hsecond
    (fun v hv => (hout v hv).symm) hlen hYuniq (head_mem hP.2.1) hzX hyX hpnX
  have heven := Thm183EvenLength.even_pathLength_of_ends_only_XComplete
    G hG.1.1.1 Y hYa P z pn hP.1 (fun v hv => (hout v hv).2)
    hlen hP.2.1 hP.2.2 hYuniq
  have h211 := _root_.Workspace.Statements.S02.SPGT.thm_2_11
    G hG.1.1.1.1.1 X Y hXY hXne hYne hXa hYa hcompl P z pn hP.1
    (fun v hv h => h.elim (hout v hv).1 (hout v hv).2)
    heven hlong hP.2.1 hP.2.2 hXuniq hYuniq
  rcases h211 with ⟨a, ha, hanti⟩ | ⟨a, ha, b, hb, hab, habP⟩
  · exact ⟨a, ha, fun v hv => hanti v (List.dropLast_subset _ hv)⟩
  · exact ⟨b, hb, Thm232Claim5SecondOutcome.last_anticomplete_dropLast habP⟩

/-- The same conclusion on the interior of `T`, using the inclusion stored
by `Claim5PathData.tailContains`. -/
theorem exists_anticomplete_tail (G : SimpleGraph V) (hG : InF8 G)
    (X Y : Set V) (hXY : Disjoint X Y) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXa : AnticonnectedSet G X) (hYa : AnticonnectedSet G Y)
    (hcompl : Complete G X Y) (P T : List V) (z y pn : V)
    (hP : IsPathFrom G P z pn) (hsecond : P.tail.head? = some y)
    (hout : ∀ v ∈ P, v ∉ X ∧ v ∉ Y) (hlong : 4 ≤ pathLength P)
    (hYuniq : ∀ v ∈ P, VertexComplete G v Y ↔ v = z ∨ v = pn)
    (hzX : VertexComplete G z X) (hyX : ¬ VertexComplete G y X)
    (hpnX : ¬ VertexComplete G pn X)
    (hcontains : ∀ v ∈ SPGT.interior T, v ∈ P.tail)
    (hnc : ∀ v ∈ SPGT.interior T, ¬ VertexComplete G v Y) :
    ∃ a ∈ X, VertexAnticomplete G a {v : V | v ∈ SPGT.interior T} := by
  obtain ⟨a, ha, hanti⟩ := exists_anticomplete_interior G hG X Y hXY hXne hYne
    hXa hYa hcompl P z y pn hP hsecond hout hlong hYuniq hzX hyX hpnX
  refine ⟨a, ha, fun v hv => hanti v ?_⟩
  apply List.mem_dropLast_of_mem_of_ne_getLast? (hcontains v hv)
  have hlen : 5 ≤ P.length := by unfold pathLength at hlong; omega
  rw [List.getLast?_tail, if_neg (by omega), hP.2.2]
  intro he
  have hpnY := (hYuniq pn (getLast_mem hP.2.2)).mpr (Or.inr rfl)
  exact hnc v hv (Option.some_injective _ he ▸ hpnY)

end Workspace.ProofLemmas.Thm232Claim5FromPath
