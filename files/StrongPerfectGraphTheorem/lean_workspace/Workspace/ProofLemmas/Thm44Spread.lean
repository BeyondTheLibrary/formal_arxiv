import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.SkewTools
import Workspace.ProofLemmas.PathInteriorIn
import Workspace.Statements.S04.Thm_4_3

/-!
# Moving a path between two fixed ends into any component of `A`

PAPER (proof of 4.4, printed p. 16): *"Now let `2 ≤ i ≤ m` and `1 ≤ j ≤ n`.  Since `(A,B)` is
not loose, `b_j` and `b_j'` both have neighbours in `A_i`, and so there is a path `P₂` say
joining them with interior in `A_i`; it is odd by 4.3, and so `(A_i,B_j)` is a path pair."*

The same sentence occurs a second time in the last paragraph of the printed proof (*"Let
`2 ≤ i ≤ m`.  Since `b₁` and `b₁'` both have neighbours in `A_i`, they are joined by a path with
interior in `A_i`, odd by 4.3"*), and a third time in the complement.  It is isolated here.

The three ingredients are exactly the three the paper names: *not loose* supplies the neighbour
in `A_i` (first bullet of *loose*), connectedness of the component supplies the path, and 4.3
supplies its parity — for if the new path were even, the old odd path and it would be two paths
of opposite parity between the same two vertices of `B` with interior in `A`, which is the first
alternative of 4.3 and would make `(A,B)` loose.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm44Spread

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.SkewTools Workspace.Types.SkewTools.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **"Since `(A,B)` is not loose, `b_j` and `b_j'` both have neighbours in `A_i`, and so there
is a path `P₂` say joining them with interior in `A_i`; it is odd by 4.3."** -/
theorem spread {G : SimpleGraph V} (hG : Berge G) {A B : Set V}
    (hAB : IsSkewPartition G A B) (hnl : ¬ IsLooseSkewPartition G A B)
    {u v : V} (hu : u ∈ B) (hv : v ∈ B)
    {Q : List V} (hQ : IsPathFrom G Q u v)
    (hQint : ∀ x ∈ SPGT.interior Q, x ∈ A) (hQodd : Odd (pathLength Q))
    {A' : Set V} (hA' : IsComponent G A A') :
    ∃ R : List V, IsPathFrom G R u v ∧ (∀ x ∈ SPGT.interior R, x ∈ A') ∧
      Odd (pathLength R) := by
  -- *"Since `(A,B)` is not loose, `b_j` and `b_j'` both have neighbours in `A_i`"*
  have hnb : ∀ b ∈ B, ∀ C : Set V, IsComponent G A C → ∃ x ∈ C, G.Adj b x := by
    intro b hb C hC
    by_contra hcon
    push_neg at hcon
    exact hnl ⟨hAB, Or.inl ⟨b, hb, C, hC, fun x hx => hcon x hx⟩⟩
  have hunotA' : u ∉ A' := fun h => (Set.disjoint_left.mp hAB.2.1) (hA'.1 h) hu
  have hvnotA' : v ∉ A' := fun h => (Set.disjoint_left.mp hAB.2.1) (hA'.1 h) hv
  -- *"and so there is a path `P₂` say joining them with interior in `A_i`"*
  obtain ⟨R, hR, hRint⟩ := Workspace.ProofLemmas.PathInteriorIn.exists_path_interior_in
    hA'.2.1 hunotA' hvnotA' (hnb u hu A' hA') (hnb v hv A' hA')
  refine ⟨R, hR, hRint, ?_⟩
  -- *"it is odd by 4.3"*
  by_contra hodd
  exact hnl (Workspace.Statements.S04.SPGT.thm_4_3 G hG A B hAB
    (Or.inl ⟨u, v, Q, R, hu, hv, hQ, hQint, hQodd, hR,
      fun x hx => hA'.1 (hRint x hx), Nat.not_odd_iff_even.mp hodd⟩)).1

end Workspace.ProofLemmas.Thm44Spread
