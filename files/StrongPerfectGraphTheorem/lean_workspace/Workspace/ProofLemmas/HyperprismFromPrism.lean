import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.NinePrismLineGraph
import Workspace.ProofLemmas.ExtremalChoice
import Workspace.ProofLemmas.HyperprismBasics

/-!
# From an even prism to a maximal hyperprism

The opening move of the proof of **10.6** (printed p. 60): *"Since `G` contains an even
prism, we can choose in `G` a collection of nine sets … We call this collection of nine sets
a hyperprism.  Let `H` be the subgraph of `G` induced on the union of the nine sets.  Choose
the hyperprism with `V(H)` maximal."*

Two things happen there and both are supplied here.

* `isHyperprism_of_isEvenPrism` — an even prism *is* a hyperprism, with
  `Aᵢ = {aᵢ}`, `Bᵢ = {bᵢ}`, `Cᵢ = V(Rᵢ)*`.  The only non-formal point is that `Cᵢ` must be
  **nonempty**, which is where *even* is used: a prism path has length `≥ 1` (its ends are
  distinct), so an *even* one has length `≥ 2` and therefore a nonempty interior.
* `exists_maximal_hyperprism` — `ExtremalChoice.exists_max_nat` over the triple of families,
  with measure `(hyperVerts A B C).ncard`.

Along the way the module records, publicly, the three facts about `FormPrism` that the
paper uses without comment and that were previously buried inside the proof of
`NinePrismLineGraph.ninePrism_isLineGraphOfBipartite`: `formPrism_path` (the family form of
the three `IsPathFrom` clauses), `formPrism_cross` (the cross-condition for an arbitrary
ordered pair `i ≠ j`, not only for the three listed pairs) and `formPrism_disjoint` (**the
three paths of a prism are pairwise vertex-disjoint**).
-/

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.HyperprismFromPrism

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.HyperprismBasics

variable {V : Type*} {G : SimpleGraph V}

/-! ### `FormPrism`, read off a `Fin 3`-indexed family of paths -/

private theorem flip_cross {P Q : List V} {a₁ a₂ b₁ b₂ : V}
    (hc : ∀ u ∈ P, ∀ v ∈ Q, (G.Adj u v ↔ (u = a₁ ∧ v = a₂) ∨ (u = b₁ ∧ v = b₂))) :
    ∀ u ∈ Q, ∀ v ∈ P, (G.Adj u v ↔ (u = a₂ ∧ v = a₁) ∨ (u = b₂ ∧ v = b₁)) := by
  intro u hu v hv
  rw [SimpleGraph.adj_comm, hc v hv u hu]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨h2, h1⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨h2, h1⟩

theorem formPrism_path {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) (i : Fin 3) : IsPathFrom G (R i) (a i) (b i) := by
  rcases fin3_cases i with rfl | rfl | rfl
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2.1

theorem formPrism_two_le_length {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) (i : Fin 3) : 2 ≤ (R i).length :=
  two_le_length_of_ends_ne (formPrism_path h i) (h.2.2.1 i i)

/-- The cross-condition of a prism, for an **arbitrary** ordered pair of distinct indices
(the definition lists only `(1,2)`, `(1,3)`, `(2,3)`). -/
theorem formPrism_cross {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) {i j : Fin 3} (hij : i ≠ j) :
    ∀ u ∈ R i, ∀ v ∈ R j, (G.Adj u v ↔ (u = a i ∧ v = a j) ∨ (u = b i ∧ v = b j)) := by
  rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl
  · exact absurd rfl hij
  · exact h.2.2.2.2.2.2.1
  · exact h.2.2.2.2.2.2.2.1
  · exact flip_cross h.2.2.2.2.2.2.1
  · exact absurd rfl hij
  · exact h.2.2.2.2.2.2.2.2
  · exact flip_cross h.2.2.2.2.2.2.2.1
  · exact flip_cross h.2.2.2.2.2.2.2.2
  · exact absurd rfl hij

/-- **The three paths of a prism are pairwise vertex-disjoint.**  Not a clause of
`FormPrism`, but a consequence: a common vertex `u ∈ V(Rᵢ) ∩ V(Rⱼ)` has a neighbour on each
of the two paths, so the two cross-conditions force `u ∈ {aᵢ,bᵢ}` and `u ∈ {aⱼ,bⱼ}`, and
those two sets are disjoint. -/
theorem formPrism_disjoint {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) {i j : Fin 3} (hij : i ≠ j) :
    ∀ u ∈ R i, u ∉ R j := by
  intro u hu huj
  obtain ⟨v, hv, hadjv⟩ :=
    NinePrismLineGraph.has_neighbour (formPrism_path h j).1 (formPrism_two_le_length h j) huj
  obtain ⟨v', hv', hadjv'⟩ :=
    NinePrismLineGraph.has_neighbour (formPrism_path h i).1 (formPrism_two_le_length h i) hu
  have h1 := (formPrism_cross h hij u hu v hv).mp hadjv
  have h2 := (formPrism_cross h hij.symm u huj v' hv').mp hadjv'
  rcases h1 with ⟨e1, -⟩ | ⟨e1, -⟩ <;> rcases h2 with ⟨e2, -⟩ | ⟨e2, -⟩
  · exact (h.1 i j hij).ne (e1.symm.trans e2)
  · exact h.2.2.1 i j (e1.symm.trans e2)
  · exact h.2.2.1 j i (e2.symm.trans e1)
  · exact (h.2.1 i j hij).ne (e1.symm.trans e2)

/-! ### An even prism is a hyperprism -/

/-- The nine sets attached to a prism: `Aᵢ = {aᵢ}`, `Bᵢ = {bᵢ}`, `Cᵢ = V(Rᵢ)*`. -/
def prismA (a : Fin 3 → V) (i : Fin 3) : Set V := {a i}

/-- See `prismA`. -/
def prismB (b : Fin 3 → V) (i : Fin 3) : Set V := {b i}

/-- See `prismA`. -/
def prismC (R : Fin 3 → List V) (i : Fin 3) : Set V := {v : V | v ∈ SPGT.interior (R i)}

theorem prismC_subset {R : Fin 3 → List V} (i : Fin 3) {v : V} (hv : v ∈ prismC R i) :
    v ∈ R i := PathBasics.interior_subset hv

/-- A vertex of `Aᵢ ∪ Bᵢ ∪ Cᵢ` lies on `Rᵢ`. -/
theorem mem_R_of_mem_S {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) (i : Fin 3) {v : V}
    (hv : v ∈ prismA a i ∪ prismB b i ∪ prismC R i) : v ∈ R i := by
  rcases hv with (hv | hv) | hv
  · rw [show v = a i from hv]
    exact PathBasics.head_mem (formPrism_path h i).2.1
  · rw [show v = b i from hv]
    exact PathBasics.getLast_mem (formPrism_path h i).2.2
  · exact prismC_subset i hv

theorem three_le_length_of_even {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) {i : Fin 3} (hev : Even (SPGT.pathLength (R i))) :
    3 ≤ (R i).length := by
  have h2 := formPrism_two_le_length h i
  rw [PathBasics.pathLength_eq, Nat.even_iff] at hev
  omega

/-- **An even prism is a hyperprism.**  (Printed p. 60, the opening sentence of the proof of
10.6.) -/
theorem isHyperprism_of_isEvenPrism {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : IsEvenPrism G a b (R 0) (R 1) (R 2)) :
    IsHyperprism G (prismA a) (prismB b) (prismC R) := by
  obtain ⟨hp, hev0, hev1, hev2⟩ := h
  have hev : ∀ i : Fin 3, Even (SPGT.pathLength (R i)) := by
    intro i; rcases fin3_cases i with rfl | rfl | rfl
    exacts [hev0, hev1, hev2]
  -- `Cᵢ` is nonempty, because an even prism path has length `≥ 2`.
  have hCne : ∀ i : Fin 3, (prismC R i).Nonempty := by
    intro i
    have hne := PathBasics.interior_ne_nil (formPrism_path hp i).1
      (three_le_length_of_even hp (hev i))
    obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hne
    exact ⟨w, hw⟩
  -- `aᵢ`, `bᵢ` are internal vertices of no `Rⱼ`.
  have haC : ∀ i j : Fin 3, a i ∉ prismC R j := by
    intro i j hcon
    by_cases hij : i = j
    · rw [hij] at hcon
      exact ((PathBasics.mem_interior_iff_of_pathFrom (formPrism_path hp j)).mp hcon).2.1 rfl
    · exact formPrism_disjoint hp hij (a i)
        (PathBasics.head_mem (formPrism_path hp i).2.1) (prismC_subset j hcon)
  have hbC : ∀ i j : Fin 3, b i ∉ prismC R j := by
    intro i j hcon
    by_cases hij : i = j
    · rw [hij] at hcon
      exact ((PathBasics.mem_interior_iff_of_pathFrom (formPrism_path hp j)).mp hcon).2.2 rfl
    · exact formPrism_disjoint hp hij (b i)
        (PathBasics.getLast_mem (formPrism_path hp i).2.2) (prismC_subset j hcon)
  refine ⟨fun i => ⟨⟨a i, rfl⟩, ⟨b i, rfl⟩, hCne i⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `Disjoint (A i) (B j)`
    intro i j
    refine Set.disjoint_left.mpr ?_
    intro x hx hx'
    exact hp.2.2.1 i j ((show x = a i from hx).symm.trans (show x = b j from hx'))
  · -- `Disjoint (A i) (C j)`
    intro i j
    refine Set.disjoint_left.mpr ?_
    intro x hx hx'
    rw [show x = a i from hx] at hx'
    exact haC i j hx'
  · -- `Disjoint (B i) (C j)`
    intro i j
    refine Set.disjoint_left.mpr ?_
    intro x hx hx'
    rw [show x = b i from hx] at hx'
    exact hbC i j hx'
  · -- `Disjoint (A i) (A j)`, `i ≠ j`
    intro i j hij
    refine Set.disjoint_left.mpr ?_
    intro x hx hx'
    exact (hp.1 i j hij).ne ((show x = a i from hx).symm.trans (show x = a j from hx'))
  · -- `Disjoint (B i) (B j)`, `i ≠ j`
    intro i j hij
    refine Set.disjoint_left.mpr ?_
    intro x hx hx'
    exact (hp.2.1 i j hij).ne ((show x = b i from hx).symm.trans (show x = b j from hx'))
  · -- `Disjoint (C i) (C j)`, `i ≠ j`
    intro i j hij
    refine Set.disjoint_left.mpr ?_
    intro x hx hx'
    exact formPrism_disjoint hp hij x (prismC_subset i hx) (prismC_subset j hx')
  · -- the complete pairs, and no other edges
    intro i j hij
    refine ⟨?_, ?_, ?_⟩
    · intro x hx y hy
      rw [show x = a i from hx, show y = a j from hy]
      exact hp.1 i j (ne_of_lt hij)
    · intro x hx y hy
      rw [show x = b i from hx, show y = b j from hy]
      exact hp.2.1 i j (ne_of_lt hij)
    · intro u hu v hv hadj
      rcases (formPrism_cross hp (ne_of_lt hij) u (mem_R_of_mem_S hp i hu) v
        (mem_R_of_mem_S hp j hv) ).mp hadj with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl ⟨e1, e2⟩
      · exact Or.inr ⟨e1, e2⟩
  · -- every vertex of `Sᵢ` lies on an `i`-rung, namely `Rᵢ` itself
    intro i v hv
    exact ⟨R i, ⟨a i, b i, rfl, rfl, formPrism_path hp i, fun w hw => hw⟩,
      mem_R_of_mem_S hp i hv⟩
  · -- some `1`-rung is even
    exact ⟨R 0, ⟨a 0, b 0, rfl, rfl, formPrism_path hp 0, fun w hw => hw⟩, hev 0⟩

theorem hyperVerts_prism {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) :
    hyperVerts (prismA a) (prismB b) (prismC R) =
      {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2} := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_hyperVerts_iff.mp hx
    have hmem : x ∈ R i := mem_R_of_mem_S h i hi
    rcases fin3_cases i with rfl | rfl | rfl
    · exact Or.inl (Or.inl hmem)
    · exact Or.inl (Or.inr hmem)
    · exact Or.inr hmem
  · intro hx
    have key : ∀ i : Fin 3, x ∈ R i → x ∈ hyperVerts (prismA a) (prismB b) (prismC R) := by
      intro i hi
      refine mem_hyperVerts_iff.mpr ⟨i, ?_⟩
      by_cases hxa : x = a i
      · exact Or.inl (Or.inl hxa)
      by_cases hxb : x = b i
      · exact Or.inl (Or.inr hxb)
      · exact Or.inr
          ((PathBasics.mem_interior_iff_of_pathFrom (formPrism_path h i)).mpr ⟨hi, hxa, hxb⟩)
    rcases hx with (hx | hx) | hx
    · exact key 0 hx
    · exact key 1 hx
    · exact key 2 hx

/-! ### Choosing the hyperprism with `V(H)` maximal -/

/-- *"Choose the hyperprism with `V(H)` maximal."*  (Printed p. 60.) -/
theorem exists_maximal_hyperprism [Fintype V]
    (h : ∃ A B C : Fin 3 → Set V, IsHyperprism G A B C) :
    ∃ A B C : Fin 3 → Set V, IsHyperprism G A B C ∧
      ∀ A' B' C' : Fin 3 → Set V, IsHyperprism G A' B' C' →
        (hyperVerts A' B' C').ncard ≤ (hyperVerts A B C).ncard := by
  obtain ⟨A, B, C, hABC⟩ := h
  obtain ⟨⟨A₀, B₀, C₀⟩, hp, hmax⟩ :=
    ExtremalChoice.exists_max_nat
      (fun t : (Fin 3 → Set V) × (Fin 3 → Set V) × (Fin 3 → Set V) =>
        IsHyperprism G t.1 t.2.1 t.2.2)
      (fun t => (hyperVerts t.1 t.2.1 t.2.2).ncard) (Fintype.card V)
      (fun t _ => ExtremalChoice.ncard_le_card _) ⟨(A, B, C), hABC⟩
  exact ⟨A₀, B₀, C₀, hp, fun A' B' C' h' => hmax (A', B', C') h'⟩

/-- The opening move of the proof of 10.6, packaged: an even prism yields a hyperprism whose
`V(H)` is maximal among **all** hyperprisms of `G`. -/
theorem exists_maximal_hyperprism_of_evenPrism [Fintype V]
    (h : ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃) :
    ∃ A B C : Fin 3 → Set V, IsHyperprism G A B C ∧
      ∀ A' B' C' : Fin 3 → Set V, IsHyperprism G A' B' C' →
        (hyperVerts A' B' C').ncard ≤ (hyperVerts A B C).ncard := by
  obtain ⟨a, b, R₁, R₂, R₃, hprism⟩ := h
  refine exists_maximal_hyperprism ⟨prismA a, prismB b, prismC ![R₁, R₂, R₃], ?_⟩
  refine isHyperprism_of_isEvenPrism (R := ![R₁, R₂, R₃]) ?_
  simpa using hprism

end Workspace.ProofLemmas.HyperprismFromPrism
