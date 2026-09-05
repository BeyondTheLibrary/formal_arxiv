import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.ProofLemmas.HyperprismFromPrism
import Workspace.ProofLemmas.Thm104NoMajor
import Workspace.ProofLemmas.Thm101CaseOneK4AppearanceWitness

/-!
# 10.1.1's last conjunct: a prism plus a two-ended connecting path is an appearance of `K₄`

PAPER (statement 10.1, alternative 1, printed p. 56):

> *"`f₁` has two adjacent neighbours in `R₁`, and `fₙ` has two adjacent neighbours in `R₂`, and
> there are no other edges between `{f₁, …, fₙ}` and `V(K)`, **and (therefore) `G` has an
> induced subgraph which is the line graph of a bipartite subdivision of `K₄`**, or"*

The bracketed *"(therefore)"* is the whole content of this module: given the first three
clauses of 10.1.1, produce `Appears G K₄`, i.e. `∃ n (H : SimpleGraph (Fin n)) (K' : Set V),
IsAppearance G K₄ H K'`.

## Why it is true, and what the proof has to build

The prism `K` is the line graph of the *theta graph* `Θ`: two branch-vertices `x, y` joined by
three internally disjoint paths of lengths `pathLength (R i) + 1`, the `j`-th vertex of `R i`
being the `j`-th edge of the `i`-th branch (this is the same dictionary that
`Workspace.ProofLemmas.NinePrismLineGraph` sets up for the special case where all three paths
have length `2`; there is no reusable general version of it in `ProofLemmas` yet, so it has to
be built here).

Two adjacent vertices `u, u'` of `R₁` are two `Θ`-edges sharing an internal vertex `z` of the
first branch, and `z` has no other `Θ`-edge, so a vertex `f₁` of `G` whose only `K`-neighbours
are `u` and `u'` is exactly a new `Θ`-edge at `z`.  Likewise `fₙ` is a new edge at an internal
vertex `z'` of the second branch, and `f₂, …, fₙ₋₁` (which by hypothesis have no `K`-neighbours
at all) subdivide the new branch.  So `H := Θ + (a new `z`–`z'` branch of length `n`)` has
four vertices of degree three — `x, y, z, z'` — and six branches

```
x–z,  z–y,  x–z',  z'–y,  x–y,  z–z',
```

that is, `H` is a subdivision of `K₄`, and `L(H) ≅ G|(V(K) ∪ {f₁, …, fₙ})`.

`H` is *bipartite* — which is what `IsAppearance` requires — exactly when every triangle of
`K₄` lifts to an even cycle.  The two triangles `x z y` and `x z' y` are even because the three
paths `R₁, R₂, R₃` of a prism in a **Berge** graph have lengths of the same parity (7.2), and
the two triangles `x z z'` and `y z z'` are even because otherwise the corresponding cycle of
`L(H)` is an odd hole of `G`.

## Deviation from the scoping lane's signature: `Berge G` is load-bearing

The scoped signature carried no `hG : Berge G`, and without it the statement is **false**.
Counterexample: let `R₀ = [a₀, b₀]`, `R₁ = [a₁, b₁]`, `R₂ = [a₂, m, b₂]` form a prism, and let
`f = [f]` be a single vertex adjacent to exactly `a₀, b₀, a₁, b₁`.  Every hypothesis below
holds (with `u, u' := a₀, b₀` and `w, w' := a₁, b₁`), and `G` has eight vertices; but a
bipartite subdivision of `K₄` has at least eight edges, and the only one with exactly eight has
minimum degree `3` in its line graph, whereas `G` has the degree-`2` vertex `m`.  So
`Appears G K₄` fails.  (That `G` is not Berge is no accident: `R₀` has odd length and `R₂` even
length, and `a₀-a₂-m-b₂-b₀-a₀` is a `5`-hole — this is exactly the configuration 7.2 rules out,
and 7.2 is what the bipartiteness of the subdivision rests on.)  `hG` is therefore stated here
in the same position as in the other four 10.1 carve-outs, and the 10.1 call site has it
verbatim.

**Call site**: the proof of `Workspace.Statements.S10.SPGT.thm_10_1`, wherever alternative
10.1.1 is concluded — from `Thm101ClaimOne` (the `c₁, d₁` adjacent branch of claim (1)) and
from `Thm101Endgame` (its final sentence).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm101K4Appearance

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **10.1.1, last conjunct**: *"… and (therefore) `G` has an induced subgraph which is the line
graph of a bipartite subdivision of `K₄`"*.

`u, u'` are the two adjacent neighbours of `f₁` in `R₁`, and `w, w'` those of `fₙ` in `R₂`;
`hno` is *"there are no other edges between `{f₁, …, fₙ}` and `V(K)`"*. -/
theorem appears_K4_of_case_one (G : SimpleGraph V) (hG : Berge G)
    (a b : Fin 3 → V) (R : Fin 3 → List V)
    (K : Set V) (f : List V) (f₁ fn u u' w w' : V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hf : IsPathFrom G f f₁ fn) (hfK : ∀ x ∈ f, x ∈ Kᶜ)
    (hu : u ∈ R 0) (hu' : u' ∈ R 0) (huu' : G.Adj u u')
    (hf₁u : G.Adj f₁ u) (hf₁u' : G.Adj f₁ u')
    (hw : w ∈ R 1) (hw' : w' ∈ R 1) (hww' : G.Adj w w')
    (hfnw : G.Adj fn w) (hfnw' : G.Adj fn w')
    (hno : ∀ x ∈ f, ∀ k ∈ K, G.Adj x k →
      (x = f₁ ∧ (k = u ∨ k = u')) ∨ (x = fn ∧ (k = w ∨ k = w'))) :
    Appears G (⊤ : SimpleGraph (Fin 4)) := by
  classical
  let F : Set V := {x : V | x ∈ f}
  obtain ⟨_, _, hab, hR0, hR1, hR2, _, _, _⟩ := id hprism
  have ha0R0 : a 0 ∈ R 0 := List.mem_of_mem_head? hR0.2.1
  have hb0R0 : b 0 ∈ R 0 := List.mem_of_mem_getLast? hR0.2.2
  have ha2R2 : a 2 ∈ R 2 := List.mem_of_mem_head? hR2.2.1
  have hb2R2 : b 2 ∈ R 2 := List.mem_of_mem_getLast? hR2.2.2
  have hdisjoint : ∀ {i j : Fin 3}, i ≠ j → ∀ x ∈ R i, x ∉ R j := by
    intro i j hij
    exact Workspace.ProofLemmas.HyperprismFromPrism.formPrism_disjoint hprism hij
  have hnoR2 : ∀ x ∈ F, ∀ k ∈ R 2, ¬ G.Adj x k := by
    intro x hx k hk hadj
    have hkK : k ∈ K := by
      rw [hK]
      exact Or.inr hk
    rcases hno x hx k hkK hadj with hx0 | hx1
    · rcases hx0.2 with hku | hku'
      · subst k
        exact hdisjoint (by decide : (0 : Fin 3) ≠ 2) u hu hk
      · subst k
        exact hdisjoint (by decide : (0 : Fin 3) ≠ 2) u' hu' hk
    · rcases hx1.2 with hkw | hkw'
      · subst k
        exact hdisjoint (by decide : (1 : Fin 3) ≠ 2) w hw hk
      · subst k
        exact hdisjoint (by decide : (1 : Fin 3) ≠ 2) w' hw' hk
  have hFK : F ⊆ Kᶜ := by
    intro x hx
    exact hfK x hx
  have hEvenNoMajor :
      IsEvenPrism G a b (R 0) (R 1) (R 2) →
        ∀ x ∈ F, ¬ MajorForPrism G a b x := by
    intro heven x hx hmajor
    have key : ∀ c : Fin 3 → V,
        2 ≤ (({c 0, c 1, c 2} : Set V) ∩ G.neighborSet x).ncard →
        ¬ G.Adj x (c 2) → G.Adj x (c 0) ∧ G.Adj x (c 1) := by
      intro c hc hc2
      constructor
      · by_contra hc0
        have hsub :
            ({c 0, c 1, c 2} : Set V) ∩ G.neighborSet x ⊆ ({c 1} : Set V) := by
          rintro z ⟨hz, hzx⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rw [SimpleGraph.mem_neighborSet] at hzx
          rcases hz with rfl | rfl | rfl
          · exact absurd hzx hc0
          · rfl
          · exact absurd hzx hc2
        have hle := Set.ncard_le_ncard hsub (Set.finite_singleton _)
        rw [Set.ncard_singleton] at hle
        omega
      · by_contra hc1
        have hsub :
            ({c 0, c 1, c 2} : Set V) ∩ G.neighborSet x ⊆ ({c 0} : Set V) := by
          rintro z ⟨hz, hzx⟩
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rw [SimpleGraph.mem_neighborSet] at hzx
          rcases hz with rfl | rfl | rfl
          · rfl
          · exact absurd hzx hc1
          · exact absurd hzx hc2
        have hle := Set.ncard_le_ncard hsub (Set.finite_singleton _)
        rw [Set.ncard_singleton] at hle
        omega
    obtain ⟨hxa0, _⟩ := key a hmajor.1 (hnoR2 x hx (a 2) ha2R2)
    obtain ⟨hxb0, _⟩ := key b hmajor.2 (hnoR2 x hx (b 2) hb2R2)
    have ownR0 : ∀ k ∈ R 0, G.Adj x k → k = u ∨ k = u' := by
      intro k hk hadj
      have hkK : k ∈ K := by
        rw [hK]
        exact Or.inl (Or.inl hk)
      rcases hno x hx k hkK hadj with hx0 | hx1
      · exact hx0.2
      · rcases hx1.2 with hkw | hkw'
        · subst k
          exact False.elim (hdisjoint (by decide : (0 : Fin 3) ≠ 1) w hk hw)
        · subst k
          exact False.elim (hdisjoint (by decide : (0 : Fin 3) ≠ 1) w' hk hw')
    have ha0pair : a 0 = u ∨ a 0 = u' := ownR0 (a 0) ha0R0 hxa0
    have hb0pair : b 0 = u ∨ b 0 = u' := ownR0 (b 0) hb0R0 hxb0
    have ha0b0 : G.Adj (a 0) (b 0) := by
      rcases ha0pair with ha | ha <;> rcases hb0pair with hb | hb
      · exact False.elim (hab 0 0 (ha.trans hb.symm))
      · simpa [ha, hb] using huu'
      · simpa [ha, hb] using huu'.symm
      · exact False.elim (hab 0 0 (ha.trans hb.symm))
    have hR0one : pathLength (R 0) = 1 := by
      have hpos : 0 < (R 0).length :=
        Workspace.ProofLemmas.PathBasics.path_length_pos hR0.1
      have hfirst : (R 0)[0]'hpos = a 0 :=
        Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hR0.2.1 hpos
      have hlast : (R 0)[(R 0).length - 1]'(by omega) = b 0 :=
        Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hR0.2.2 hpos
      have hidx := (Workspace.ProofLemmas.PathBasics.path_adj_iff hR0.1 hpos
        (show (R 0).length - 1 < (R 0).length by omega)).mp (by
          rw [hfirst, hlast]
          exact ha0b0)
      rw [Workspace.ProofLemmas.PathBasics.pathLength_eq]
      omega
    have hR0even : Even (pathLength (R 0)) := heven.2.1
    rw [hR0one] at hR0even
    rcases hR0even with ⟨q, hq⟩
    omega
  have hR2attachments : ∀ k ∈ attachments G F K, k ∉ R 2 := by
    intro k hk hkR2
    rcases hk with ⟨_, x, hx, hkx⟩
    exact hnoR2 x hx k hkR2 hkx.symm
  have hfNonmajor : ∀ x ∈ f, ¬ MajorForPrism G a b x := by
    have hall := Workspace.ProofLemmas.Thm104NoMajor.thm104_no_major
      G hG a b R K F hprism hK hFK hEvenNoMajor hR2attachments
    intro x hx
    exact hall x hx
  obtain ⟨m, H, K', _, happearance, _⟩ :=
    Workspace.ProofLemmas.Thm101CaseOneK4AppearanceWitness
      G hG a b R K f f₁ fn u u' w w' hprism hK hf hfK hfNonmajor
        hu hu' huu' hf₁u hf₁u' hw hw' hww' hfnw hfnw' hno
  exact ⟨m, H, K', happearance⟩

end Workspace.ProofLemmas.Thm101K4Appearance
