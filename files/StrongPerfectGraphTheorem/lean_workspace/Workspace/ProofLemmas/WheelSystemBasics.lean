import Mathlib
import Workspace.Types.Core
import Workspace.Types.WheelSystems

/-!
# Bookkeeping for frames and wheel systems (§19)

Sections 19–23 are written entirely in the vocabulary of `Workspace.Types.WheelSystems`, and
they use the following facts about `wheelSystemX` and `wheelSystemA` silently, on almost every
page.  None of them is a numbered statement of the paper.

`wheelSystemX x i` is the paper's `Xᵢ = {x₀,…,xᵢ}`; it is monotone in `i`.

`wheelSystemA G z A₀ x i` is the paper's `Aᵢ`, defined in the type module as the union of the
family

> `𝒜ᵢ = { A | A₀ ⊆ A, A connected, A contains no neighbour of z, A contains no Xᵢ-complete
> vertex }`.

The paper says *"`Aᵢ` is **the maximal** connected subset of `V(G)` that includes `A₀`, contains
no neighbour of `z`, and contains no `Xᵢ`-complete vertex"*, so the union has to be shown to be
a member of `𝒜ᵢ` before it deserves the name.  Three of the four clauses are inherited by any
union (they are pointwise, or a `⊆`); connectedness is the one with content, and it holds
because every member of `𝒜ᵢ` contains the *nonempty* set `A₀`, so any two vertices of the union
are joined through `A₀` inside the union.  That is `connectedSet_wheelSystemA` below.

The paper's remark *"So for each `i`, `A_{i−1} ⊆ Aᵢ`"* is `wheelSystemA_mono`: it holds because
`Xᵢ₋₁ ⊆ Xᵢ`, so being `Xᵢ`-complete is a *stronger* condition than being `Xᵢ₋₁`-complete, so the
constraint *"contains no `Xᵢ`-complete vertex"* is weaker and the family `𝒜ᵢ` is larger.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.WheelSystemBasics

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## `Xᵢ = {x₀, …, xᵢ}` -/

theorem mem_wheelSystemX {x : ℕ → V} {i : ℕ} {v : V} :
    v ∈ wheelSystemX x i ↔ ∃ j ≤ i, v = x j := Iff.rfl

theorem self_mem_wheelSystemX (x : ℕ → V) {i j : ℕ} (h : j ≤ i) :
    x j ∈ wheelSystemX x i := ⟨j, h, rfl⟩

theorem wheelSystemX_mono (x : ℕ → V) {i j : ℕ} (h : i ≤ j) :
    wheelSystemX x i ⊆ wheelSystemX x j := by
  rintro v ⟨k, hk, rfl⟩
  exact ⟨k, hk.trans h, rfl⟩

theorem wheelSystemX_zero (x : ℕ → V) : wheelSystemX x 0 = {x 0} := by
  ext v
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [Nat.le_zero.mp hk]
    rfl
  · rintro rfl
    exact ⟨0, le_rfl, rfl⟩

theorem wheelSystemX_one (x : ℕ → V) : wheelSystemX x 1 = {x 0, x 1} := by
  ext v
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨1, le_rfl, rfl⟩

/-- Being `Xⱼ`-complete for a larger `j` is a stronger condition. -/
theorem vertexComplete_wheelSystemX_mono {G : SimpleGraph V} {x : ℕ → V} {i j : ℕ} (h : i ≤ j)
    {v : V} (hv : VertexComplete G v (wheelSystemX x j)) :
    VertexComplete G v (wheelSystemX x i) :=
  fun w hw => hv w (wheelSystemX_mono x h hw)

/-! ## `Aᵢ`, the maximal connected set avoiding `z` and the `Xᵢ`-complete vertices -/

/-- The defining family of `Aᵢ`. -/
def Fam (G : SimpleGraph V) (z : V) (A₀ : Set V) (x : ℕ → V) (i : ℕ) : Set (Set V) :=
  {A : Set V | A₀ ⊆ A ∧ ConnectedSet G A ∧ (∀ v ∈ A, ¬ G.Adj z v) ∧
    (∀ v ∈ A, ¬ VertexComplete G v (wheelSystemX x i))}

theorem wheelSystemA_eq (G : SimpleGraph V) (z : V) (A₀ : Set V) (x : ℕ → V) (i : ℕ) :
    wheelSystemA G z A₀ x i = ⋃₀ Fam G z A₀ x i := rfl

theorem mem_wheelSystemA {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {i : ℕ} {v : V} :
    v ∈ wheelSystemA G z A₀ x i ↔ ∃ A ∈ Fam G z A₀ x i, v ∈ A := Iff.rfl

/-- Any member of the family is contained in `Aᵢ`. -/
theorem subset_wheelSystemA {G : SimpleGraph V} {z : V} {A₀ A : Set V} {x : ℕ → V} {i : ℕ}
    (hA : A ∈ Fam G z A₀ x i) : A ⊆ wheelSystemA G z A₀ x i :=
  fun _ hv => ⟨A, hA, hv⟩

/-- `Aᵢ` contains no neighbour of `z`. -/
theorem wheelSystemA_no_nbr {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {i : ℕ}
    {v : V} (hv : v ∈ wheelSystemA G z A₀ x i) : ¬ G.Adj z v := by
  obtain ⟨A, hA, hvA⟩ := hv
  exact hA.2.2.1 v hvA

/-- `Aᵢ` contains no `Xᵢ`-complete vertex. -/
theorem wheelSystemA_no_complete {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {i : ℕ}
    {v : V} (hv : v ∈ wheelSystemA G z A₀ x i) :
    ¬ VertexComplete G v (wheelSystemX x i) := by
  obtain ⟨A, hA, hvA⟩ := hv
  exact hA.2.2.2 v hvA

/-- `A₀ ⊆ Aᵢ`, whenever `A₀` itself belongs to the family — which for a frame `(z, A₀)` means
exactly that no vertex of `A₀` is `Xᵢ`-complete. -/
theorem A₀_subset_wheelSystemA {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {i : ℕ}
    (hframe : IsFrame G z A₀)
    (hnc : ∀ v ∈ A₀, ¬ VertexComplete G v (wheelSystemX x i)) :
    A₀ ⊆ wheelSystemA G z A₀ x i :=
  subset_wheelSystemA ⟨subset_rfl, hframe.2.1, hframe.2.2.2, hnc⟩

/-- `A₀` itself is a member of the family, under the same proviso. -/
theorem A₀_mem_Fam {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {i : ℕ}
    (hframe : IsFrame G z A₀)
    (hnc : ∀ v ∈ A₀, ¬ VertexComplete G v (wheelSystemX x i)) :
    A₀ ∈ Fam G z A₀ x i :=
  ⟨subset_rfl, hframe.2.1, hframe.2.2.2, hnc⟩

private theorem reachable_induce_mono {H : SimpleGraph V} {A B : Set V}
    (hAB : A ⊆ B) {u v : V} (hu : u ∈ A) (hv : v ∈ A)
    (hr : (H.induce A).Reachable ⟨u, hu⟩ ⟨v, hv⟩) :
    (H.induce B).Reachable ⟨u, hAB hu⟩ ⟨v, hAB hv⟩ := by
  obtain ⟨p⟩ := hr
  exact ⟨SimpleGraph.Walk.map
    (⟨fun w => ⟨w.1, hAB w.2⟩, fun {_ _} hab => hab⟩ : (H.induce A) →g (H.induce B)) p⟩

/-- **`Aᵢ` really is connected** — the clause that makes the union deserve the paper's name
*"the maximal connected subset …"*.  Every member of the family contains the nonempty set `A₀`,
so any two vertices of the union are joined through `A₀` without leaving the union. -/
theorem connectedSet_wheelSystemA {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {i : ℕ}
    (hne : A₀.Nonempty) : ConnectedSet G (wheelSystemA G z A₀ x i) := by
  obtain ⟨a, ha⟩ := hne
  have hamem : a ∈ wheelSystemA G z A₀ x i → True := fun _ => trivial
  -- every vertex of the union reaches `a`
  have key : ∀ u : ↥(wheelSystemA G z A₀ x i), ∀ (haU : a ∈ wheelSystemA G z A₀ x i),
      (G.induce (wheelSystemA G z A₀ x i)).Reachable u ⟨a, haU⟩ := by
    rintro ⟨u, hu⟩ haU
    obtain ⟨A, hA, huA⟩ := hu
    have hsub : A ⊆ wheelSystemA G z A₀ x i := subset_wheelSystemA hA
    have haA : a ∈ A := hA.1 ha
    exact reachable_induce_mono hsub huA haA (hA.2.1 ⟨u, huA⟩ ⟨a, haA⟩)
  intro u v
  by_cases haU : a ∈ wheelSystemA G z A₀ x i
  · exact (key u haU).trans (key v haU).symm
  · exact absurd (u.2) (by
      intro hu
      obtain ⟨A, hA, _⟩ := hu
      exact haU (subset_wheelSystemA hA (hA.1 ha)))

/-- The paper's *"So for each `i`, `A_{i−1} ⊆ Aᵢ`"*. -/
theorem wheelSystemA_mono {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {i j : ℕ}
    (h : i ≤ j) : wheelSystemA G z A₀ x i ⊆ wheelSystemA G z A₀ x j := by
  rintro v ⟨A, hA, hvA⟩
  exact ⟨A, ⟨hA.1, hA.2.1, hA.2.2.1, fun w hw hc =>
    hA.2.2.2 w hw (vertexComplete_wheelSystemX_mono h hc)⟩, hvA⟩

/-- The membership test the section proofs actually use: a connected set including `A₀`, with no
neighbour of `z` and no `Xᵢ`-complete vertex, has all its vertices in `Aᵢ`.  This is the
*"condition 2 above just says that `xᵢ` has a neighbour in `A_{i−1}`"* direction. -/
theorem mem_wheelSystemA_of_witness {G : SimpleGraph V} {z : V} {A₀ B : Set V} {x : ℕ → V}
    {i : ℕ} (hA₀ : A₀ ⊆ B) (hcon : ConnectedSet G B) (hz : ∀ v ∈ B, ¬ G.Adj z v)
    (hX : ∀ v ∈ B, ¬ VertexComplete G v (wheelSystemX x i)) {b : V} (hb : b ∈ B) :
    b ∈ wheelSystemA G z A₀ x i :=
  ⟨B, ⟨hA₀, hcon, hz, hX⟩, hb⟩

/-- Consequently the existential form of `IsWheelSystem`'s condition 2 is equivalent to the
`Aᵢ` form: *"`xᵢ` has a neighbour in `A_{i−1}`"*. -/
theorem exists_adj_wheelSystemA_of_witness {G : SimpleGraph V} {z : V} {A₀ B : Set V}
    {x : ℕ → V} {i : ℕ} (hA₀ : A₀ ⊆ B) (hcon : ConnectedSet G B) (hz : ∀ v ∈ B, ¬ G.Adj z v)
    (hX : ∀ v ∈ B, ¬ VertexComplete G v (wheelSystemX x i)) {u : V}
    (hu : ∃ b ∈ B, G.Adj u b) :
    ∃ a ∈ wheelSystemA G z A₀ x i, G.Adj u a := by
  obtain ⟨b, hb, hub⟩ := hu
  exact ⟨b, mem_wheelSystemA_of_witness hA₀ hcon hz hX hb, hub⟩

end Workspace.ProofLemmas.WheelSystemBasics
