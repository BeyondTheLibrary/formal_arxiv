import Mathlib
import Workspace.Types.Core
import Workspace.Types.Knots
import Workspace.ProofLemmas.PathBasics

/-!
# Striations under complementation — the "*by taking complements*" transport of §9

Section 9 of *The Strong Perfect Graph Theorem* (Chudnovsky, Robertson, Seymour, Thomas),
printed pages 50–51.  The proof of 9.6 says *"by taking complements"* four separate times; this
module supplies exactly the transport that phrase abbreviates.

Three parenthetical remarks of the paper are turned into theorems here.

* In the definition of a **striation** (printed p. 50): *"(Note that if we replace some
  `(Aᵢ, Cᵢ, Bᵢ)` by its reverse, we obtain another striation.)"* — and, more to the point for
  us, the exchange of strips and antistrips that goes with passing to `Ḡ`.  That is
  `isStriation_compl` / `maximalStriation_compl`.
* In the definition of a **twist** (printed p. 50): *"We call the quadruple `(S₁, S₂, T₁, T₂)` a
  twist if `S₁, S₂` agree on one of `T₁, T₂` and disagree on the other.  (Equivalently, if
  `T₁, T₂` agree on one of `S₁, S₂`, and disagree on the other.)"* — that is `isTwist_compl`.
* In the definition of **resolves** (printed p. 51): *"We say `X` resolves `L` if `V(L) \ X` is
  local with respect to the striation in `Ḡ` obtained from `L` by exchanging the strips and
  antistrips; that is, if …"* — the paper asserts that its two forms agree, which is
  `resolves_iff_local_compl` (and its dual `local_iff_resolves_compl`).

## The one trap

`SPGT.Complete Gᶜ P Q` is `∀ p ∈ P, ∀ q ∈ Q, p ≠ q ∧ ¬ G.Adj p q`, which is *strictly stronger*
than `SPGT.Anticomplete G P Q`; dually `SPGT.Anticomplete Gᶜ P Q` says `p = q ∨ G.Adj p q`, which
is weaker than `SPGT.Complete G P Q`.  The missing `p ≠ q` is why every transport lemma below
carries a disjointness hypothesis.  `complete_compl_iff` and `anticomplete_compl_iff` are the two
bridges, and every other proof in this file goes through them.

## Reading off the four bullets

Write `S = (A, C, B)` and `T = (X, Z, Y)`.  Then

* `ParallelStripAntistrip G S T` is: `A` complete to `X ∪ Z`, `B` complete to `Y ∪ Z`,
  `X` anticomplete to `B ∪ C`, `Y` anticomplete to `A ∪ C`;
* `ParallelStripAntistrip Gᶜ T S` (so `T` occupies the *strip* slot) is: `X` complete-in-`Gᶜ` to
  `A ∪ C`, `Y` complete-in-`Gᶜ` to `B ∪ C`, `A` anticomplete-in-`Gᶜ` to `Y ∪ Z`,
  `B` anticomplete-in-`Gᶜ` to `X ∪ Z`, which under disjointness is: `X` anticomplete to `A ∪ C`,
  `Y` anticomplete to `B ∪ C`, `A` complete to `Y ∪ Z`, `B` complete to `X ∪ Z`;
* `CoParallel G S T = ParallelStripAntistrip G (A, C, B) (Y, Z, X)` is: `A` complete to `Y ∪ Z`,
  `B` complete to `X ∪ Z`, `Y` anticomplete to `B ∪ C`, `X` anticomplete to `A ∪ C`.

The second and third lists coincide — that is `parallel_compl`, and `coParallel_compl` is the
same computation with `S` reversed.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.StriationCompl

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT

variable {V : Type*}

/-! ### The two bridging lemmas -/

/-- Two points of disjoint sets are distinct. -/
private theorem ne_of_disjoint {P Q : Set V} (h : Disjoint P Q) {x y : V}
    (hx : x ∈ P) (hy : y ∈ Q) : x ≠ y := by
  rintro rfl
  exact Set.disjoint_left.mp h hx hy

/-- `Complete Gᶜ P Q` unfolds to `∀ p ∈ P, ∀ q ∈ Q, p ≠ q ∧ ¬ G.Adj p q`, so it is
`Anticomplete G P Q` **plus** the disequalities; under `Disjoint P Q` the two agree. -/
theorem complete_compl_iff {G : SimpleGraph V} {P Q : Set V} (h : Disjoint P Q) :
    SPGT.Complete Gᶜ P Q ↔ SPGT.Anticomplete G P Q := by
  constructor
  · intro hc x hx y hy
    exact (hc x hx y hy).2
  · intro ha x hx y hy
    exact ⟨ne_of_disjoint h hx hy, ha x hx y hy⟩

/-- `Anticomplete Gᶜ P Q` unfolds to `∀ p ∈ P, ∀ q ∈ Q, p = q ∨ G.Adj p q`, so it is
`Complete G P Q` **minus** the disequalities; under `Disjoint P Q` the two agree. -/
theorem anticomplete_compl_iff {G : SimpleGraph V} {P Q : Set V} (h : Disjoint P Q) :
    SPGT.Anticomplete Gᶜ P Q ↔ SPGT.Complete G P Q := by
  constructor
  · intro ha x hx y hy
    by_contra hadj
    exact ha x hx y hy ⟨ne_of_disjoint h hx hy, hadj⟩
  · intro hc x hx y hy hadj
    exact hadj.2 (hc x hx y hy)

/-! ### Vertex-set bookkeeping -/

/-- Every vertex of an `S`-rung lies in `V(S)`: the first vertex is in `A`, the last in `B`, and
everything else is interior, hence in `C`.  (Printed p. 50: *"every vertex of `A ∪ B ∪ C` belongs
to a path between `A` and `B` with only its first vertex in `A`, only its last vertex in `B`, and
interior in `C`"*.) -/
private theorem mem_stripVertices_of_isSRung {H : SimpleGraph V} {R : Set V × Set V × Set V}
    {p : List V} (hR : IsSRung H R p) {x : V} (hx : x ∈ p) : x ∈ stripVertices R := by
  obtain ⟨A, C, B⟩ := R
  obtain ⟨a, b, hpath, haA, hbB, -, -, hint⟩ := hR
  show x ∈ A ∪ B ∪ C
  by_cases hxa : x = a
  · subst hxa
    exact Set.mem_union_left _ (Set.mem_union_left _ haA)
  · by_cases hxb : x = b
    · subst hxb
      exact Set.mem_union_left _ (Set.mem_union_right _ hbB)
    · exact Set.mem_union_right _
        (hint x ((PathBasics.mem_interior_iff_of_pathFrom hpath).mpr ⟨hx, hxa, hxb⟩))

/-- `V(Sᵢ) ⊆ V(L)`. -/
theorem stripVertices_S_subset {m n : ℕ} (S : Fin m → Set V × Set V × Set V)
    (T : Fin n → Set V × Set V × Set V) (i : Fin m) :
    stripVertices (S i) ⊆ striationVertices S T := by
  intro x hx
  exact Set.mem_union_left _ (Set.mem_iUnion_of_mem i hx)

/-- `V(Tⱼ) ⊆ V(L)`. -/
theorem stripVertices_T_subset {m n : ℕ} (S : Fin m → Set V × Set V × Set V)
    (T : Fin n → Set V × Set V × Set V) (j : Fin n) :
    stripVertices (T j) ⊆ striationVertices S T := by
  intro x hx
  exact Set.mem_union_right _ (Set.mem_iUnion_of_mem j hx)

/-- Every vertex of an `Sᵢ`-rung lies in `V(L)`. -/
theorem mem_striationVertices_of_isSRung {H : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    {i : Fin m} {p : List V} (hR : IsSRung H (S i) p) {x : V} (hx : x ∈ p) :
    x ∈ striationVertices S T :=
  stripVertices_S_subset S T i (mem_stripVertices_of_isSRung hR hx)

/-- Every vertex of a `Tⱼ`-antirung lies in `V(L)`. -/
theorem mem_striationVertices_of_isSRung' {H : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    {j : Fin n} {p : List V} (hR : IsSRung H (T j) p) {x : V} (hx : x ∈ p) :
    x ∈ striationVertices S T :=
  stripVertices_T_subset S T j (mem_stripVertices_of_isSRung hR hx)

/-! ### `V(L)` does not see the strip/antistrip labelling -/

/-- **`V(L)` is symmetric in the two families.**  Printed p. 50: *"the union of the vertex sets of
all its strips and antistrips"* — a union, so the order is immaterial. -/
theorem striationVertices_swap {m n : ℕ}
    (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V) :
    striationVertices T S = striationVertices S T :=
  Set.union_comm _ _

/-! ### Strips and antistrips exchange under complementation -/

/-- **A strip of `G` is an antistrip of `Gᶜ`.**  Printed p. 50: *"An antistrip is a triple that is
a strip in `Ḡ`."* -/
theorem isAntistrip_compl {G : SimpleGraph V} {S : Set V × Set V × Set V} :
    IsAntistrip Gᶜ S ↔ IsStrip G S := by
  rw [IsAntistrip, compl_compl]

/-- **An antistrip of `G` is a strip of `Gᶜ`** — this is the definition. -/
theorem isStrip_compl {G : SimpleGraph V} {T : Set V × Set V × Set V} :
    IsStrip Gᶜ T ↔ IsAntistrip G T := Iff.rfl

/-! ### Parallel and co-parallel exchange under complementation -/

/-- **Parallel becomes co-parallel under complementation with the roles exchanged.**

`ParallelStripAntistrip Gᶜ T S` puts the antistrip `T` into the *strip* slot of `Gᶜ`; reading off
the four bullets and applying `complete_compl_iff` / `anticomplete_compl_iff` gives exactly
`ParallelStripAntistrip G (A, C, B) (Y, Z, X)`, i.e. `CoParallel G S T`. -/
theorem parallel_compl {G : SimpleGraph V} {S T : Set V × Set V × Set V}
    (hd : Disjoint (stripVertices S) (stripVertices T)) :
    ParallelStripAntistrip Gᶜ T S ↔ CoParallel G S T := by
  obtain ⟨A, C, B⟩ := S
  obtain ⟨X, Z, Y⟩ := T
  have hd' : Disjoint (A ∪ B ∪ C) (X ∪ Y ∪ Z) := hd
  have sA : A ⊆ A ∪ B ∪ C := fun z hz => Or.inl (Or.inl hz)
  have sB : B ⊆ A ∪ B ∪ C := fun z hz => Or.inl (Or.inr hz)
  have sC : C ⊆ A ∪ B ∪ C := fun z hz => Or.inr hz
  have sX : X ⊆ X ∪ Y ∪ Z := fun z hz => Or.inl (Or.inl hz)
  have sY : Y ⊆ X ∪ Y ∪ Z := fun z hz => Or.inl (Or.inr hz)
  have sZ : Z ⊆ X ∪ Y ∪ Z := fun z hz => Or.inr hz
  have dXAC : Disjoint X (A ∪ C) := hd'.symm.mono sX (Set.union_subset sA sC)
  have dYBC : Disjoint Y (B ∪ C) := hd'.symm.mono sY (Set.union_subset sB sC)
  have dAYZ : Disjoint A (Y ∪ Z) := hd'.mono sA (Set.union_subset sY sZ)
  have dBXZ : Disjoint B (X ∪ Z) := hd'.mono sB (Set.union_subset sX sZ)
  simp only [ParallelStripAntistrip, CoParallel, reverseStrip]
  rw [complete_compl_iff dXAC, complete_compl_iff dYBC,
    anticomplete_compl_iff dAYZ, anticomplete_compl_iff dBXZ]
  tauto

/-- **Co-parallel becomes parallel under complementation with the roles exchanged.** -/
theorem coParallel_compl {G : SimpleGraph V} {S T : Set V × Set V × Set V}
    (hd : Disjoint (stripVertices S) (stripVertices T)) :
    CoParallel Gᶜ T S ↔ ParallelStripAntistrip G S T := by
  obtain ⟨A, C, B⟩ := S
  obtain ⟨X, Z, Y⟩ := T
  have hd' : Disjoint (A ∪ B ∪ C) (X ∪ Y ∪ Z) := hd
  have sA : A ⊆ A ∪ B ∪ C := fun z hz => Or.inl (Or.inl hz)
  have sB : B ⊆ A ∪ B ∪ C := fun z hz => Or.inl (Or.inr hz)
  have sC : C ⊆ A ∪ B ∪ C := fun z hz => Or.inr hz
  have sX : X ⊆ X ∪ Y ∪ Z := fun z hz => Or.inl (Or.inl hz)
  have sY : Y ⊆ X ∪ Y ∪ Z := fun z hz => Or.inl (Or.inr hz)
  have sZ : Z ⊆ X ∪ Y ∪ Z := fun z hz => Or.inr hz
  have dXBC : Disjoint X (B ∪ C) := hd'.symm.mono sX (Set.union_subset sB sC)
  have dYAC : Disjoint Y (A ∪ C) := hd'.symm.mono sY (Set.union_subset sA sC)
  have dBYZ : Disjoint B (Y ∪ Z) := hd'.mono sB (Set.union_subset sY sZ)
  have dAXZ : Disjoint A (X ∪ Z) := hd'.mono sA (Set.union_subset sX sZ)
  simp only [ParallelStripAntistrip, CoParallel, reverseStrip]
  rw [complete_compl_iff dXBC, complete_compl_iff dYAC,
    anticomplete_compl_iff dBYZ, anticomplete_compl_iff dAXZ]
  tauto

/-- **A strip and an antistrip cannot be both parallel and co-parallel.**

If both held then `A` would be complete to `X` (from parallel) while `X` is anticomplete to `A`
(from co-parallel); and `A`, `X` are nonempty because `IsStrip` / `IsAntistrip` demand that the
two end-sets be nonempty.  This is what makes "parallel-or-co-parallel" a genuine *bit*, which is
the content of the paper's parenthetical equivalence in the definition of a twist. -/
theorem not_parallel_and_coParallel {G : SimpleGraph V} {S T : Set V × Set V × Set V}
    (hS : IsStrip G S) (hT : IsAntistrip G T) :
    ¬ (ParallelStripAntistrip G S T ∧ CoParallel G S T) := by
  obtain ⟨A, C, B⟩ := S
  obtain ⟨X, Z, Y⟩ := T
  rintro ⟨hp, hc⟩
  simp only [ParallelStripAntistrip, CoParallel, reverseStrip] at hp hc
  simp only [IsStrip] at hS
  simp only [IsAntistrip, IsStrip] at hT
  obtain ⟨a, ha⟩ := hS.2.2.2.1
  obtain ⟨x, hx⟩ := hT.2.2.2.1
  have h1 : G.Adj a x := hp.1.1 a ha x (Set.mem_union_left _ hx)
  have h2 : ¬ G.Adj x a := hc.2.2 x hx a (Set.mem_union_left _ ha)
  exact h2 h1.symm

/-! ### Twists -/

/-- **The paper's "(Equivalently, …)" in the definition of a twist** (printed p. 50):
*"We call the quadruple `(S₁, S₂, T₁, T₂)` a twist if `S₁, S₂` agree on one of `T₁, T₂` and
disagree on the other.  (Equivalently, if `T₁, T₂` agree on one of `S₁, S₂`, and disagree on the
other.)"*

Give the pair `(Sᵢ, Tⱼ)` the bit `bᵢⱼ = 0` if parallel and `1` if co-parallel — well defined by
`not_parallel_and_coParallel` together with the hypotheses `hpcᵢⱼ`.  Then `IsTwist G S₁ S₂ T₁ T₂`
says `b₁₁ + b₂₁ + b₁₂ + b₂₂` is odd, and so does `IsTwist Gᶜ T₁ T₂ S₁ S₂` after transporting each
bit by `parallel_compl` / `coParallel_compl` (which flip it, uniformly). -/
theorem isTwist_compl {G : SimpleGraph V} {S₁ S₂ T₁ T₂ : Set V × Set V × Set V}
    (hS₁ : IsStrip G S₁) (hS₂ : IsStrip G S₂)
    (hT₁ : IsAntistrip G T₁) (hT₂ : IsAntistrip G T₂)
    (hd11 : Disjoint (stripVertices S₁) (stripVertices T₁))
    (hd12 : Disjoint (stripVertices S₁) (stripVertices T₂))
    (hd21 : Disjoint (stripVertices S₂) (stripVertices T₁))
    (hd22 : Disjoint (stripVertices S₂) (stripVertices T₂))
    (hpc11 : ParallelStripAntistrip G S₁ T₁ ∨ CoParallel G S₁ T₁)
    (hpc12 : ParallelStripAntistrip G S₁ T₂ ∨ CoParallel G S₁ T₂)
    (hpc21 : ParallelStripAntistrip G S₂ T₁ ∨ CoParallel G S₂ T₁)
    (hpc22 : ParallelStripAntistrip G S₂ T₂ ∨ CoParallel G S₂ T₂) :
    IsTwist Gᶜ T₁ T₂ S₁ S₂ ↔ IsTwist G S₁ S₂ T₁ T₂ := by
  have n11 := not_parallel_and_coParallel hS₁ hT₁
  have n12 := not_parallel_and_coParallel hS₁ hT₂
  have n21 := not_parallel_and_coParallel hS₂ hT₁
  have n22 := not_parallel_and_coParallel hS₂ hT₂
  simp only [IsTwist, AgreeOn]
  rw [parallel_compl hd11, parallel_compl hd12, parallel_compl hd21, parallel_compl hd22,
    coParallel_compl hd11, coParallel_compl hd12, coParallel_compl hd21, coParallel_compl hd22]
  rcases hpc11 with h11 | h11 <;> rcases hpc12 with h12 | h12 <;>
    rcases hpc21 with h21 | h21 <;> rcases hpc22 with h22 | h22 <;> tauto

/-! ### Striations -/

/-- **Exchanging the strips and the antistrips turns a striation of `G` into a striation of `Gᶜ`.**

Printed p. 51, in the definition of *resolves*: *"the striation in `Ḡ` obtained from `L` by
exchanging the strips and antistrips"* — the paper takes for granted that this really is a
striation; here it is.  Clause by clause: strips and antistrips swap by `isStrip_compl` /
`isAntistrip_compl` and `compl_compl`; the complete/anticomplete clauses swap by the two bridging
lemmas, fed with the pairwise-disjointness clauses the striation already carries; the
parallel/co-parallel clause swaps by `parallel_compl` / `coParallel_compl`; and the two twist
clauses swap by `isTwist_compl`. -/
theorem isStriation_compl {G : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (h : IsStriation G S T) : IsStriation Gᶜ T S := by
  obtain ⟨hS, hT, hSS, hTT, hST, hSrung, hTrung, hm, hn, hSanti, hTcomp, hpc, htw1, htw2⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the `Tⱼ` are strips of `Gᶜ`
    exact hT
  · -- the `Sᵢ` are antistrips of `Gᶜ`
    intro i
    show IsStrip Gᶜᶜ (S i)
    rw [compl_compl]
    exact hS i
  · exact hTT
  · exact hSS
  · exact fun j i => (hST i j).symm
  · exact hTrung
  · -- `Sᵢ`-antirungs of `Gᶜ` are exactly `Sᵢ`-rungs of `G`
    intro i p hp
    rw [compl_compl] at hp
    exact hSrung i p hp
  · exact hn
  · exact hm
  · -- `Tⱼ` complete to `Tⱼ'` in `G` becomes anticomplete in `Gᶜ`
    intro j j' hjj'
    exact (anticomplete_compl_iff (hTT j j' (ne_of_lt hjj'))).mpr (hTcomp j j' hjj')
  · -- `Sᵢ` anticomplete to `Sᵢ'` in `G` becomes complete in `Gᶜ`
    intro i i' hii'
    exact (complete_compl_iff (hSS i i' (ne_of_lt hii'))).mpr (hSanti i i' hii')
  · -- parallel and co-parallel exchange
    intro j i
    rcases hpc i j with hp | hcp
    · exact Or.inr ((coParallel_compl (hST i j)).mpr hp)
    · exact Or.inl ((parallel_compl (hST i j)).mpr hcp)
  · -- twists witnessing pairs of strips of `Gᶜ` (= antistrips of `G`)
    intro j j' hjj'
    obtain ⟨i, i', hii', htw⟩ := htw2 j j' hjj'
    exact ⟨i, i', hii',
      (isTwist_compl (hS i) (hS i') (hT j) (hT j') (hST i j) (hST i j') (hST i' j) (hST i' j')
        (hpc i j) (hpc i j') (hpc i' j) (hpc i' j')).mpr htw⟩
  · -- twists witnessing pairs of antistrips of `Gᶜ` (= strips of `G`)
    intro i i' hii'
    obtain ⟨j, j', hjj', htw⟩ := htw1 i i' hii'
    exact ⟨j, j', hjj',
      (isTwist_compl (hS i) (hS i') (hT j) (hT j') (hST i j) (hST i j') (hST i' j) (hST i' j')
        (hpc i j) (hpc i j') (hpc i' j) (hpc i' j')).mpr htw⟩

/-- **A maximal striation of `G` gives a maximal striation of `Gᶜ`.**

A striation `(S', T')` of `Gᶜ` with `V(L) ⊂ V(L')` gives, by `isStriation_compl` and
`compl_compl`, a striation `(T', S')` of `G` with the same vertex set (`striationVertices_swap`),
contradicting maximality in `G`. -/
theorem maximalStriation_compl {G : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (h : MaximalStriation G S T) : MaximalStriation Gᶜ T S := by
  refine ⟨isStriation_compl h.1, ?_⟩
  rintro ⟨m', n', S', T', hstr', hlt⟩
  refine h.2 ⟨n', m', T', S', ?_, ?_⟩
  · have hback := isStriation_compl hstr'
    rwa [compl_compl] at hback
  · rw [striationVertices_swap S' T']
    rwa [striationVertices_swap S T] at hlt

/-! ### `resolves` and `local` exchange under complementation -/

/-- **The paper's own definition of "resolves", made into a theorem** (printed p. 51):
*"We say `X` resolves `L` if `V(L) \ X` is local with respect to the striation in `Ḡ` obtained
from `L` by exchanging the strips and antistrips; that is, if • there is at most one of
`T₁, …, T_n` that is not a subset of `X`, • for `1 ≤ i ≤ m`, every `Sᵢ`-rung meets `X`, and • `X`
contains at least one end of every edge between `V(S₁) ∪ ⋯ ∪ V(S_m)` and `V(T₁) ∪ ⋯ ∪ V(T_n)`."*

The three clauses match one by one.  (1) uses `V(Tⱼ) ⊆ V(L)`, so
`(V(L) \ X) ∩ V(Tⱼ) = V(Tⱼ) \ X`, whose nonemptiness is `¬ V(Tⱼ) ⊆ X`.  (2) uses
`IsSRung Gᶜᶜ (Sᵢ) = IsSRung G (Sᵢ)` and the fact that a rung's vertices lie in `V(L)`, so that
`v ∉ V(L) \ X ↔ v ∈ X` along the rung.  (3) is the contrapositive, the disequality `u ≠ w` coming
from the striation's own disjointness clause. -/
theorem resolves_iff_local_compl {G : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (hL : IsStriation G S T) {X : Set V} (hX : X ⊆ striationVertices S T) :
    ResolvesStriation G S T X ↔
      LocalForStriation Gᶜ T S (striationVertices S T \ X) := by
  have hdisj : ∀ (i : Fin m) (j : Fin n),
      Disjoint (stripVertices (S i)) (stripVertices (T j)) := hL.2.2.2.2.1
  have hb1 : ∀ j : Fin n,
      ((striationVertices S T \ X) ∩ stripVertices (T j)).Nonempty ↔
        ¬ (stripVertices (T j) ⊆ X) := by
    intro j
    constructor
    · rintro ⟨v, ⟨-, hvX⟩, hvT⟩ hsub
      exact hvX (hsub hvT)
    · intro hns
      obtain ⟨v, hvT, hvX⟩ := Set.not_subset.mp hns
      exact ⟨v, ⟨stripVertices_T_subset S T j hvT, hvX⟩, hvT⟩
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro j j' hj hj'
      exact h1 j j' ((hb1 j).mp hj) ((hb1 j').mp hj')
    · intro i p hp
      rw [compl_compl] at hp
      obtain ⟨v, hvp, hvX⟩ := h2 i p hp
      exact ⟨v, hvp, fun hc => hc.2 hvX⟩
    · intro u hu w hw
      obtain ⟨⟨-, huX⟩, huT⟩ := hu
      obtain ⟨⟨-, hwX⟩, hwS⟩ := hw
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp huT
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hwS
      refine ⟨(ne_of_disjoint (hdisj i j) hi hj).symm, ?_⟩
      intro hadj
      rcases h3 w hwS u huT hadj.symm with hc | hc
      · exact hwX hc
      · exact huX hc
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro j j' hj hj'
      exact h1 j j' ((hb1 j).mpr hj) ((hb1 j').mpr hj')
    · intro i p hp
      have hp' : IsSRung Gᶜᶜ (S i) p := by rwa [compl_compl]
      obtain ⟨v, hvp, hv⟩ := h2 i p hp'
      refine ⟨v, hvp, ?_⟩
      by_contra hvX
      exact hv ⟨mem_striationVertices_of_isSRung (T := T) hp hvp, hvX⟩
    · intro u hu w hw hadj
      by_contra hcon
      push_neg at hcon
      obtain ⟨huX, hwX⟩ := hcon
      have huL : u ∈ striationVertices S T := Set.mem_union_left _ hu
      have hwL : w ∈ striationVertices S T := Set.mem_union_right _ hw
      exact (h3 w ⟨⟨hwL, hwX⟩, hw⟩ u ⟨⟨huL, huX⟩, hu⟩).2 hadj.symm

/-- **The dual of `resolves_iff_local_compl`**: being local for `L` in `G` is resolving the
exchanged striation in `Ḡ`.  Same three clause-by-clause matches, read the other way. -/
theorem local_iff_resolves_compl {G : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (hL : IsStriation G S T) {X : Set V} (hX : X ⊆ striationVertices S T) :
    LocalForStriation G S T X ↔
      ResolvesStriation Gᶜ T S (striationVertices S T \ X) := by
  have hdisj : ∀ (i : Fin m) (j : Fin n),
      Disjoint (stripVertices (S i)) (stripVertices (T j)) := hL.2.2.2.2.1
  have hb1 : ∀ i : Fin m,
      (X ∩ stripVertices (S i)).Nonempty ↔
        ¬ (stripVertices (S i) ⊆ striationVertices S T \ X) := by
    intro i
    constructor
    · rintro ⟨v, hvX, hvS⟩ hsub
      exact (hsub hvS).2 hvX
    · intro hns
      obtain ⟨v, hvS, hv⟩ := Set.not_subset.mp hns
      refine ⟨v, ?_, hvS⟩
      by_contra hvX
      exact hv ⟨stripVertices_S_subset S T i hvS, hvX⟩
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i i' hi hi'
      exact h1 i i' ((hb1 i).mpr hi) ((hb1 i').mpr hi')
    · intro j p hp
      obtain ⟨v, hvp, hvX⟩ := h2 j p hp
      exact ⟨v, hvp, mem_striationVertices_of_isSRung' (S := S) hp hvp, hvX⟩
    · intro u hu w hw hadj
      by_contra hcon
      push_neg at hcon
      obtain ⟨hu', hw'⟩ := hcon
      have huL : u ∈ striationVertices S T := Set.mem_union_right _ hu
      have hwL : w ∈ striationVertices S T := Set.mem_union_left _ hw
      have huX : u ∈ X := by by_contra hc; exact hu' ⟨huL, hc⟩
      have hwX : w ∈ X := by by_contra hc; exact hw' ⟨hwL, hc⟩
      exact hadj.2 (h3 w ⟨hwX, hw⟩ u ⟨huX, hu⟩).symm
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i i' hi hi'
      exact h1 i i' ((hb1 i).mp hi) ((hb1 i').mp hi')
    · intro j p hp
      obtain ⟨v, hvp, hv⟩ := h2 j p hp
      exact ⟨v, hvp, hv.2⟩
    · intro u hu w hw
      obtain ⟨huX, huS⟩ := hu
      obtain ⟨hwX, hwT⟩ := hw
      by_contra hadj
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp huS
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hwT
      have hcadj : Gᶜ.Adj w u :=
        ⟨(ne_of_disjoint (hdisj i j) hi hj).symm, fun hc => hadj hc.symm⟩
      rcases h3 w hwT u huS hcadj with hc | hc
      · exact hc.2 hwX
      · exact hc.2 huX

/-! ### The neighbourhood bridge -/

/-- **For `v ∉ L`, the `Gᶜ`-neighbours of `v` inside `L` are the complement inside `L` of its
`G`-neighbours there.**  The hypothesis `v ∉ L` is what supplies the disequality that
`Gᶜ.Adj v w` carries over `¬ G.Adj v w`. -/
theorem compl_neighborSet_inter {G : SimpleGraph V} {v : V} {L : Set V} (hv : v ∉ L) :
    Gᶜ.neighborSet v ∩ L = L \ (G.neighborSet v ∩ L) := by
  ext w
  constructor
  · rintro ⟨hadj, hwL⟩
    refine ⟨hwL, ?_⟩
    rintro ⟨hadj', -⟩
    exact hadj.2 hadj'
  · rintro ⟨hwL, hnot⟩
    refine ⟨⟨?_, ?_⟩, hwL⟩
    · rintro rfl
      exact hv hwL
    · intro hadj
      exact hnot ⟨hadj, hwL⟩

end Workspace.ProofLemmas.StriationCompl
