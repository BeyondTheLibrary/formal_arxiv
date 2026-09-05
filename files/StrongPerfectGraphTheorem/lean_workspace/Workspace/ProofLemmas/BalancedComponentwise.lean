import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.ClassLemmas

/-!
# Balancedness is checked componentwise

The proof of 4.2 (printed p. 15) ends *"It remains to check all the pairs `(A_i, B_1)` … This
proves that `(A,B)` is balanced"*: having verified that every pair `(A_i, B_j)` consisting of a
component of `A` and an anticomponent of `B` is balanced, the authors conclude that `(A,B)`
itself is balanced.  That step is left implicit, and this module supplies it.

The reason it is true: an odd path between nonadjacent vertices `u, v ∈ B` with interior in `A`
has both its ends in one anticomponent of `B` (they are nonadjacent, hence `Ḡ`-adjacent) and its
whole interior in one component of `A` (the interior of a path is connected).  Dually for
antipaths, which is the same statement in `Ḡ` with the two sides interchanged.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.BalancedComponentwise

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The interior of a path is a connected set of vertices. -/
private theorem connectedSet_interior {G : SimpleGraph V} {p : List V}
    (hp : IsPathList G p) : ConnectedSet G {x : V | x ∈ SPGT.interior p} := by
  by_cases h3 : 3 ≤ p.length
  · exact Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (Workspace.ProofLemmas.PathGlue.isPathFrom_interior hp h3).1
  · have hnil : SPGT.interior p = [] := by
      have hl := Workspace.ProofLemmas.PathBasics.interior_length p
      exact List.eq_nil_of_length_eq_zero (by omega)
    intro a b
    rw [hnil] at a
    exact absurd a.2 (by simp)

/-- A connected subset of `A` meeting a component `C` of `A` is contained in `C`. -/
private theorem subset_component {G : SimpleGraph V} {A S C : Set V}
    (hS : ConnectedSet G S) (hSA : S ⊆ A) (hC : IsComponent G A C)
    {x : V} (hxS : x ∈ S) (hxC : x ∈ C) : S ⊆ C := by
  have hcon : ConnectedSet G (C ∪ S) :=
    Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union hC.2.1 hS
      (Or.inl ⟨x, hxC, hxS⟩)
  have heq : C ∪ S = C :=
    hC.2.2 (C ∪ S) Set.subset_union_left (Set.union_subset hC.1 hSA) hcon
  intro y hy
  have : y ∈ C ∪ S := Or.inr hy
  rwa [heq] at this

/-- The path half of the statement, for an arbitrary graph; the antipath half is this
statement in `Ḡ` with the two sides interchanged. -/
private theorem clause_one {G : SimpleGraph V} {A B : Set V} (hA : A.Nonempty)
    (h : ∀ A' B' : Set V, IsComponent G A A' → IsAnticomponent G B B' →
      Workspace.Types.Core.SPGT.Balanced G A' B') :
    ∀ (u v : V) (p : List V), u ∈ B → v ∈ B → ¬ G.Adj u v → IsPathFrom G p u v →
      (∀ x ∈ SPGT.interior p, x ∈ A) → ¬ Odd (pathLength p) := by
  intro u v p hu hv hnadj hp hint hodd
  have hlen1 : 1 ≤ pathLength p := by
    obtain ⟨k, hk⟩ := hodd; omega
  have hne : u ≠ v := Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hp hlen1
  obtain ⟨B₁, hB₁, huB₁⟩ :=
    Workspace.ProofLemmas.ComponentsOfSetBasics.exists_isComponent_mem Gᶜ B hu
  obtain ⟨B₂, hB₂, hvB₂⟩ :=
    Workspace.ProofLemmas.ComponentsOfSetBasics.exists_isComponent_mem Gᶜ B hv
  have hBB : B₁ = B₂ := by
    by_contra hc
    exact Workspace.ProofLemmas.ComponentsOfSetBasics.anticomplete_of_isComponent Gᶜ hB₁ hB₂ hc
      u huB₁ v hvB₂ ⟨hne, hnadj⟩
  have huB₂ : u ∈ B₂ := hBB ▸ huB₁
  by_cases hS : ({x : V | x ∈ SPGT.interior p}).Nonempty
  · obtain ⟨w, hw⟩ := hS
    obtain ⟨A', hA', hwA'⟩ :=
      Workspace.ProofLemmas.ComponentsOfSetBasics.exists_isComponent_mem G A (hint w hw)
    have hsub : {x : V | x ∈ SPGT.interior p} ⊆ A' :=
      subset_component (connectedSet_interior hp.1) (fun x hx => hint x hx) hA' hw hwA'
    exact (h A' B₂ hA' hB₂).1 u v p huB₂ hvB₂ hnadj hp (fun x hx => hsub hx) hodd
  · obtain ⟨a, ha⟩ := hA
    obtain ⟨A', hA', -⟩ :=
      Workspace.ProofLemmas.ComponentsOfSetBasics.exists_isComponent_mem G A ha
    refine (h A' B₂ hA' hB₂).1 u v p huB₂ hvB₂ hnadj hp (fun x hx => ?_) hodd
    exact absurd (⟨x, hx⟩ : ({x : V | x ∈ SPGT.interior p}).Nonempty) hS

/-- **If every pair (component of `A`, anticomponent of `B`) is balanced, then `(A,B)` is
balanced.**  This is the last sentence of the printed proof of 4.2. -/
theorem balanced_of_components {G : SimpleGraph V} {A B : Set V}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (h : ∀ A' B' : Set V, IsComponent G A A' → IsAnticomponent G B B' →
      Workspace.Types.Core.SPGT.Balanced G A' B') :
    Workspace.Types.Core.SPGT.Balanced G A B := by
  have h' : ∀ B' A' : Set V, IsComponent Gᶜ B B' → IsAnticomponent Gᶜ A A' →
      Workspace.Types.Core.SPGT.Balanced Gᶜ B' A' := by
    intro B' A' hB' hA'
    have hA'' : IsComponent G A A' := by rwa [IsAnticomponent, compl_compl] at hA'
    exact Workspace.ProofLemmas.ClassLemmas.balanced_compl.mpr (h A' B' hA'' hB')
  refine ⟨clause_one hA h, ?_⟩
  intro u v q hu hv hadj hq hint
  refine clause_one (G := Gᶜ) (A := B) (B := A) hB h' u v q hu hv ?_ hq hint
  intro hc
  exact ((SimpleGraph.compl_adj G u v).mp hc).2 hadj

end Workspace.ProofLemmas.BalancedComponentwise
