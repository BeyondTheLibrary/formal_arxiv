import Workspace.ProofLemmas.PathBasics

/-!
# The second outcome of 2.11 in 23.2(5)

The paper concludes that one of the two rim vertices misses the interior of the
chosen path. Both outcomes of 2.11 imply this: in its second outcome, the last
endpoint only sees the last vertex of the middle path.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm232Claim5SecondOutcome

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas.PathBasics

variable {V : Type*} {G : SimpleGraph V}

/-- PAPER (23.2(5), printed p. 141): "By 2.11 ... one of `x₀,x₁` is
nonadjacent to all of `y,p₁,...,p_{k-1}`." In the second outcome of 2.11 this
is its last endpoint. The last vertex of `L` is omitted from the conclusion. -/
theorem last_anticomplete_dropLast {a b : V} {L : List V}
    (hp : IsPathList G (a :: (L ++ [b]))) :
    VertexAnticomplete G b {v : V | v ∈ L.dropLast} := by
  intro v hv hadj
  obtain ⟨i, hi, hiv⟩ := List.getElem_of_mem hv
  have hiL : i + 1 < L.length := by
    simp only [List.length_dropLast] at hi
    omega
  have heq : (a :: (L ++ [b]))[i + 1]'(by simp; omega) = v := by
    rw [List.getElem_cons_succ, List.getElem_append_left (by omega)]
    rw [List.getElem_dropLast] at hiv
    exact hiv
  have hlast : (a :: (L ++ [b]))[L.length + 1]'(by simp) = b := by
    rw [List.getElem_cons_succ, List.getElem_concat_length rfl]
  have h := (path_adj_iff hp (i := L.length + 1) (j := i + 1)
    (by simp) (by simp; omega)).mp (by rwa [hlast, heq])
  omega

/-- PAPER (23.2(5), printed p. 141): "Since
`{y,v₁,...,v_n} ⊆ {y,p₁,...,p_{k-1}}`, this proves (5)."
The stored inclusion in `P.tail` suffices: the last vertex is `Y`-complete,
whereas the interior of `T` contains no `Y`-complete vertex. -/
theorem second_outcome_anticomplete {a b pn : V} {P T : List V} {Y : Set V}
    (hlong : 2 ≤ P.length) (hlast : P.getLast? = some pn)
    (hpn : VertexComplete G pn Y)
    (hcontains : ∀ v ∈ SPGT.interior T, v ∈ P.tail)
    (hnc : ∀ v ∈ SPGT.interior T, ¬ VertexComplete G v Y)
    (hp : IsPathList G (a :: (P.tail ++ [b]))) :
    VertexAnticomplete G b {v : V | v ∈ SPGT.interior T} := by
  intro v hv
  apply last_anticomplete_dropLast hp v
  apply List.mem_dropLast_of_mem_of_ne_getLast? (hcontains v hv)
  rw [List.getLast?_tail, if_neg (by omega), hlast]
  intro heq
  exact hnc v hv (Option.some_injective _ heq ▸ hpn)

end Workspace.ProofLemmas.Thm232Claim5SecondOutcome
