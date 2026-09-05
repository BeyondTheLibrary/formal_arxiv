import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.ProofLemmas.PathBasics

/-!
# The symmetries of a labelled prism

PAPER (§10, printed p. 56, statement 10.1): *"Then there is a path `f₁-⋯-fₙ` in `F` with
`n ≥ 1`, such that **(up to symmetry)** either: …"*, and, in the printed proof, the repeated
*"we may assume …, by exchanging `A` and `B` if necessary"* / *"from the symmetry we may assume
that `c₁ ≠ a₁`"*.

The symmetry group in question is the automorphism group of the *labelled* prism: the three
paths `R₁, R₂, R₃` may be permuted by any `σ : Equiv.Perm (Fin 3)` (carrying `aᵢ, bᵢ` along),
and the two triangles `A = {a₁,a₂,a₃}` and `B = {b₁,b₂,b₃}` may be interchanged (which reverses
each `Rᵢ`).  This module records that every notion §10 uses — `FormPrism`, the vertex set `V(K)`
of the prism, `LocalForPrism`, `SaturatesPrism`, `MajorForPrism` — is invariant under both.

The only mildly non-trivial ingredient is `formPrism_family`, an equivalent *index-symmetric*
form of `FormPrism`: the definition pins the three "no other edges" clauses to the ordered pairs
`(1,2), (1,3), (2,3)`, and the permutation argument wants all six ordered pairs.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.PrismSymmetry

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT

variable {V : Type*}

/-! ### A triple `{c 0, c 1, c 2}` is the range of `c`, hence permutation-invariant -/

theorem triple_eq_range (c : Fin 3 → V) : ({c 0, c 1, c 2} : Set V) = Set.range c := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem triple_perm (c : Fin 3 → V) (σ : Equiv.Perm (Fin 3)) :
    ({c (σ 0), c (σ 1), c (σ 2)} : Set V) = ({c 0, c 1, c 2} : Set V) := by
  have h1 : ({c (σ 0), c (σ 1), c (σ 2)} : Set V) = Set.range (fun i => c (σ i)) :=
    triple_eq_range (fun i => c (σ i))
  rw [h1, triple_eq_range c]
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨σ i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨σ.symm i, by simp⟩

/-- The vertex set `V(K)` of the prism is invariant under permuting the three paths. -/
theorem prismVertices_perm (R : Fin 3 → List V) (σ : Equiv.Perm (Fin 3)) :
    ({v : V | v ∈ R (σ 0)} ∪ {v : V | v ∈ R (σ 1)} ∪ {v : V | v ∈ R (σ 2)}) =
      ({v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2}) := by
  have key : ∀ (S : Fin 3 → List V),
      ({v : V | v ∈ S 0} ∪ {v : V | v ∈ S 1} ∪ {v : V | v ∈ S 2}) =
        {v : V | ∃ i : Fin 3, v ∈ S i} := by
    intro S
    ext x
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro ((h | h) | h)
      exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
  rw [key (fun i => R (σ i)), key R]
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨σ i, hi⟩
  · rintro ⟨i, hi⟩; exact ⟨σ.symm i, by simpa using hi⟩

/-- The vertex set `V(K)` does not change when each path is reversed (which is what
interchanging the two triangles does). -/
theorem prismVertices_reverse (P₁ P₂ P₃ : List V) :
    ({v : V | v ∈ P₁.reverse} ∪ {v : V | v ∈ P₂.reverse} ∪ {v : V | v ∈ P₃.reverse}) =
      ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ P₃}) := by
  ext x; simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_reverse]

/-! ### An index-symmetric reformulation of `FormPrism` -/

/-- `FormPrism` restated with the three paths presented as a family `R : Fin 3 → List V` and
with the "no other edges" clause quantified over *all* ordered pairs of distinct indices.  This
is the form in which the permutation symmetry of the prism is evident. -/
theorem formPrism_family {G : SimpleGraph V} {a b : Fin 3 → V} {R : Fin 3 → List V} :
    FormPrism G a b (R 0) (R 1) (R 2) ↔
      ((∀ i j : Fin 3, i ≠ j → G.Adj (a i) (a j)) ∧
       (∀ i j : Fin 3, i ≠ j → G.Adj (b i) (b j)) ∧
       (∀ i j : Fin 3, a i ≠ b j) ∧
       (∀ i : Fin 3, IsPathFrom G (R i) (a i) (b i)) ∧
       (∀ i j : Fin 3, i ≠ j → ∀ u ∈ R i, ∀ v ∈ R j,
          (G.Adj u v ↔ (u = a i ∧ v = a j) ∨ (u = b i ∧ v = b j)))) := by
  constructor
  · rintro ⟨hA, hB, hAB, hp1, hp2, hp3, h12, h13, h23⟩
    refine ⟨hA, hB, hAB, ?_, ?_⟩
    · intro i; fin_cases i
      exacts [hp1, hp2, hp3]
    · -- the three given clauses, plus their mirror images obtained by `G.adj_comm`
      have mirror : ∀ (i j : Fin 3), (∀ u ∈ R i, ∀ v ∈ R j,
            (G.Adj u v ↔ (u = a i ∧ v = a j) ∨ (u = b i ∧ v = b j))) →
          (∀ u ∈ R j, ∀ v ∈ R i,
            (G.Adj u v ↔ (u = a j ∧ v = a i) ∨ (u = b j ∧ v = b i))) := by
        intro i j h u hu v hv
        rw [G.adj_comm]
        rw [h v hv u hu]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          exacts [Or.inl ⟨h2, h1⟩, Or.inr ⟨h2, h1⟩]
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          exacts [Or.inl ⟨h2, h1⟩, Or.inr ⟨h2, h1⟩]
      intro i j hij
      fin_cases i <;> fin_cases j <;> first
        | exact absurd rfl hij
        | exact h12
        | exact h13
        | exact h23
        | exact mirror 0 1 h12
        | exact mirror 0 2 h13
        | exact mirror 1 2 h23
  · rintro ⟨hA, hB, hAB, hp, hedge⟩
    exact ⟨hA, hB, hAB, hp 0, hp 1, hp 2,
      hedge 0 1 (by decide), hedge 0 2 (by decide), hedge 1 2 (by decide)⟩

/-! ### Permuting the three paths -/

/-- **The paper's "up to symmetry": permuting the three indices.**  If `R 0, R 1, R 2` form a
prism with triangles `a` and `b`, then so do `R (σ 0), R (σ 1), R (σ 2)` with triangles
`a ∘ σ` and `b ∘ σ`, for any permutation `σ` of `Fin 3`. -/
theorem formPrism_perm {G : SimpleGraph V} {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) (σ : Equiv.Perm (Fin 3)) :
    FormPrism G (fun i => a (σ i)) (fun i => b (σ i))
      ((fun i => R (σ i)) 0) ((fun i => R (σ i)) 1) ((fun i => R (σ i)) 2) := by
  obtain ⟨hA, hB, hAB, hp, hedge⟩ := formPrism_family.mp h
  refine (formPrism_family (G := G) (a := fun i => a (σ i)) (b := fun i => b (σ i))
    (R := fun i => R (σ i))).mpr ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun i j hij => hA _ _ fun hc => hij (σ.injective hc)
  · exact fun i j hij => hB _ _ fun hc => hij (σ.injective hc)
  · exact fun i j => hAB _ _
  · exact fun i => hp (σ i)
  · exact fun i j hij => hedge _ _ fun hc => hij (σ.injective hc)

/-! ### Interchanging the two triangles -/

/-- **The paper's "by exchanging `A` and `B` if necessary".**  Interchanging the two triangles
reverses each of the three paths. -/
theorem formPrism_swap {G : SimpleGraph V} {a b : Fin 3 → V} {P₁ P₂ P₃ : List V}
    (h : FormPrism G a b P₁ P₂ P₃) :
    FormPrism G b a P₁.reverse P₂.reverse P₃.reverse := by
  obtain ⟨hA, hB, hAB, hp1, hp2, hp3, h12, h13, h23⟩ := h
  refine ⟨hB, hA, fun i j => (hAB j i).symm,
    PathBasics.isPathFrom_reverse hp1, PathBasics.isPathFrom_reverse hp2,
    PathBasics.isPathFrom_reverse hp3, ?_, ?_, ?_⟩
  · intro u hu v hv
    rw [List.mem_reverse] at hu hv
    rw [h12 u hu v hv]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  · intro u hu v hv
    rw [List.mem_reverse] at hu hv
    rw [h13 u hu v hv]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  · intro u hu v hv
    rw [List.mem_reverse] at hu hv
    rw [h23 u hu v hv]
    exact ⟨fun h => h.symm, fun h => h.symm⟩

/-! ### `LocalForPrism`, `SaturatesPrism`, `MajorForPrism` are invariant -/

theorem localForPrism_perm {a b : Fin 3 → V} {R : Fin 3 → List V} {X : Set V}
    (σ : Equiv.Perm (Fin 3)) :
    LocalForPrism (fun i => a (σ i)) (fun i => b (σ i))
        ((fun i => R (σ i)) 0) ((fun i => R (σ i)) 1) ((fun i => R (σ i)) 2) X ↔
      LocalForPrism a b (R 0) (R 1) (R 2) X := by
  have hA : ({a (σ 0), a (σ 1), a (σ 2)} : Set V) = ({a 0, a 1, a 2} : Set V) := triple_perm a σ
  have hB : ({b (σ 0), b (σ 1), b (σ 2)} : Set V) = ({b 0, b 1, b 2} : Set V) := triple_perm b σ
  have hind : ∀ (Y : Set V),
      (Y ⊆ {v : V | v ∈ R (σ 0)} ∨ Y ⊆ {v : V | v ∈ R (σ 1)} ∨ Y ⊆ {v : V | v ∈ R (σ 2)}) ↔
      (Y ⊆ {v : V | v ∈ R 0} ∨ Y ⊆ {v : V | v ∈ R 1} ∨ Y ⊆ {v : V | v ∈ R 2}) := by
    intro Y
    have pack : ∀ (S : Fin 3 → List V),
        (Y ⊆ {v : V | v ∈ S 0} ∨ Y ⊆ {v : V | v ∈ S 1} ∨ Y ⊆ {v : V | v ∈ S 2}) ↔
          ∃ i : Fin 3, Y ⊆ {v : V | v ∈ S i} := by
      intro S
      constructor
      · rintro (h | h | h)
        exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
      · rintro ⟨i, hi⟩
        fin_cases i
        · exact Or.inl hi
        · exact Or.inr (Or.inl hi)
        · exact Or.inr (Or.inr hi)
    rw [pack (fun i => R (σ i)), pack R]
    constructor
    · rintro ⟨i, hi⟩; exact ⟨σ i, hi⟩
    · rintro ⟨i, hi⟩; exact ⟨σ.symm i, by simpa using hi⟩
  have weak : ∀ {A B C D E : Prop}, (A ∨ B ∨ C) → (A ∨ B ∨ C ∨ D ∨ E) :=
    fun h => h.imp id (Or.imp id Or.inl)
  unfold LocalForPrism
  constructor
  · rintro (h | h | h | h | h)
    · exact weak ((hind X).mp (Or.inl h))
    · exact weak ((hind X).mp (Or.inr (Or.inl h)))
    · exact weak ((hind X).mp (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hA ▸ h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (hB ▸ h))))
  · rintro (h | h | h | h | h)
    · exact weak ((hind X).mpr (Or.inl h))
    · exact weak ((hind X).mpr (Or.inr (Or.inl h)))
    · exact weak ((hind X).mpr (Or.inr (Or.inr h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hA ▸ h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (hB ▸ h))))

theorem localForPrism_swap {a b : Fin 3 → V} {P₁ P₂ P₃ : List V} {X : Set V} :
    LocalForPrism b a P₁.reverse P₂.reverse P₃.reverse X ↔ LocalForPrism a b P₁ P₂ P₃ X := by
  have hrev : ∀ P : List V, {v : V | v ∈ P.reverse} = {v : V | v ∈ P} := by
    intro P; ext x; simp [List.mem_reverse]
  unfold LocalForPrism
  rw [hrev P₁, hrev P₂, hrev P₃]
  constructor
  · rintro (h | h | h | h | h)
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)),
      Or.inr (Or.inr (Or.inr (Or.inr h))), Or.inr (Or.inr (Or.inr (Or.inl h)))]
  · rintro (h | h | h | h | h)
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl h)),
      Or.inr (Or.inr (Or.inr (Or.inr h))), Or.inr (Or.inr (Or.inr (Or.inl h)))]

theorem saturatesPrism_perm {a b : Fin 3 → V} {X : Set V} (σ : Equiv.Perm (Fin 3)) :
    SaturatesPrism (fun i => a (σ i)) (fun i => b (σ i)) X ↔ SaturatesPrism a b X := by
  unfold SaturatesPrism
  rw [show ({a (σ 0), a (σ 1), a (σ 2)} : Set V) = ({a 0, a 1, a 2} : Set V) from triple_perm a σ,
    show ({b (σ 0), b (σ 1), b (σ 2)} : Set V) = ({b 0, b 1, b 2} : Set V) from triple_perm b σ]

theorem saturatesPrism_swap {a b : Fin 3 → V} {X : Set V} :
    SaturatesPrism b a X ↔ SaturatesPrism a b X := by
  unfold SaturatesPrism; exact and_comm

theorem majorForPrism_perm {G : SimpleGraph V} {a b : Fin 3 → V} {v : V}
    (σ : Equiv.Perm (Fin 3)) :
    MajorForPrism G (fun i => a (σ i)) (fun i => b (σ i)) v ↔ MajorForPrism G a b v :=
  saturatesPrism_perm σ

theorem majorForPrism_swap {G : SimpleGraph V} {a b : Fin 3 → V} {v : V} :
    MajorForPrism G b a v ↔ MajorForPrism G a b v :=
  saturatesPrism_swap

end Workspace.ProofLemmas.PrismSymmetry
