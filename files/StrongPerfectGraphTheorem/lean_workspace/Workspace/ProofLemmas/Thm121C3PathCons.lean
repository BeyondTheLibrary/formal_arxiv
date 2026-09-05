import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics

/-!
# Extending a path by one vertex at the front

Both case (3) and case (4) of the printed proof of 12.1 apply 11.2 to paths that the authors
describe but do not construct: *"the path from `v` to `b₁` with interior in `R₁ \ a₁`", "let `Q`
be a path in `G \ (V(S) ∪ {a₀})` from `v` to `b₀`"*, and so on.  Every one of them is built the
same way: take a stretch of an already-known path, and put `v` in front of it.

Since the paper's *paths* are **induced** subgraphs (`Core.IsPathList` is an `↔` on indices, not
merely "consecutive entries are adjacent"), prepending a vertex is only legitimate when `v`'s
sole neighbour on the stretch is its first vertex.  That is exactly the condition the authors
arrange by choosing the neighbour of `v` **closest to the far end**, and it is the hypothesis
`hadj` below.

This is list bookkeeping, not mathematics of the paper; it belongs with
`Workspace.ProofLemmas.PathBasics`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm121C3PathCons

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*} {G : SimpleGraph V} {S : List V} {v : V}

/-- Prepending `v` to the path `S` gives a path, provided `v ∉ S` and the only vertex of `S`
adjacent to `v` is `S[0]`. -/
theorem isPathList_cons (hS : IsPathList G S) (hvS : v ∉ S)
    (hadj : ∀ (i : ℕ) (hi : i < S.length), (G.Adj v (S[i]'hi) ↔ i = 0)) :
    IsPathList G (v :: S) := by
  refine ⟨by simp, List.nodup_cons.mpr ⟨hvS, hS.2.1⟩, ?_⟩
  intro i j hi hj
  cases i with
  | zero =>
    cases j with
    | zero => simp
    | succ m =>
      have hm : m < S.length := by simpa using hj
      simp only [List.getElem_cons_zero, List.getElem_cons_succ]
      rw [hadj m hm]
      omega
  | succ n =>
    have hn : n < S.length := by simpa using hi
    cases j with
    | zero =>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ]
      rw [SimpleGraph.adj_comm, hadj n hn]
      omega
    | succ m =>
      have hm : m < S.length := by simpa using hj
      simp only [List.getElem_cons_succ]
      rw [hS.2.2 n m hn hm]
      omega

/-- The named-ends form: if `S` is a path from `x` to `b`, `v ∉ S`, and the only vertex of `S`
adjacent to `v` is `x`, then `v :: S` is a path from `v` to `b`. -/
theorem isPathFrom_cons {x b : V} (hS : IsPathFrom G S x b) (hvS : v ∉ S)
    (hadj : ∀ y ∈ S, (G.Adj v y ↔ y = x)) :
    IsPathFrom G (v :: S) v b := by
  have hne : S ≠ [] := hS.1.1
  have hlen : 0 < S.length := Workspace.ProofLemmas.PathBasics.path_length_pos hS.1
  have hx0 : S[0]'hlen = x :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hS.2.1 hlen
  refine ⟨isPathList_cons hS.1 hvS ?_, rfl, ?_⟩
  · intro i hi
    rw [hadj (S[i]'hi) (List.getElem_mem hi), ← hx0]
    exact hS.1.2.1.getElem_inj_iff
  · rcases S with _ | ⟨y, t⟩
    · exact absurd rfl hne
    · rw [List.getLast?_cons_cons]
      exact hS.2.2

end Workspace.ProofLemmas.Thm121C3PathCons
