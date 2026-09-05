import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.SkewTools
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.StripSystemNeighbourhood
import Workspace.ProofLemmas.AnticompleteUnionComponents
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.LooseSkewPartition
import Workspace.ProofLemmas.BalancedComponentwise
import Workspace.ProofLemmas.BalancedRestrictNonComplete
import Workspace.Statements.S02.Thm_2_6
import Workspace.Statements.S02.Thm_2_7
import Workspace.Statements.S04.Thm_4_1

/-!
# Section 4 — Skew partitions

The six numbered statements 4.1 – 4.6 of Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem* (published / *Annals* version; printed pages 14–18).
Every definition used here is imported, never restated:

* `Workspace.Types.Core` — `Berge`, `IsPathFrom`, `IsAntipathFrom`, `pathLength`,
  `SPGT.interior`, `IsComponent`, `IsAnticomponent`, `VertexComplete`,
  `VertexAnticomplete`, `Complete`, `Anticomplete`, `SPGT.Balanced`
* `Workspace.Types.Decompositions` — `IsSkewPartition`, `IsBalancedSkewPartition`,
  `AdmitsBalancedSkewPartition`
* `Workspace.Types.SkewTools` — `IsLooseSkewPartition`, `AdmitsLooseSkewPartition`,
  `IsPathPair`, `IsAntipathPair`, `IsKernel`

## Encoding conventions specific to this section

* A path / antipath is the list `p` of its vertices in order, with named ends via
  `IsPathFrom` / `IsAntipathFrom`; "with interior in `S`" is
  `∀ x ∈ SPGT.interior p, x ∈ S`; "odd" / "even" refer to `SPGT.pathLength p`, the number of
  edges.  (`SPGT.interior` and `SPGT.Balanced` are always written with their `SPGT.`
  prefix, since the bare names are captured by Mathlib's topological `interior` and by
  Mathlib's `Balanced` set-in-a-module predicate.)
* The paper's *"let `A₁,…,A_m` be the components of `A`, and `B₁,…,B_n` the anticomponents of
  `B`"* fixes an enumeration only in order to index the alternatives of 4.4 by `(i,j)`; since
  the published 4.4 quantifies over *all* `i,j`, the enumeration is rendered by universally
  quantifying over all components `A'` of `A` and all anticomponents `B'` of `B`.  (The
  published paper itself made this change: it indexes path/antipath pairs by the *sets*
  `(A_i,B_j)` rather than by the index pair `(i,j)`.)
* *"has only one vertex"* is `∃ a, S = {a}`.

## Published vs. arXiv v1

**4.6 is strictly stronger in the published version and it is the published form that is
transcribed here.**  The arXiv draft's hypotheses read *"joined by an even path with interior
in `A₁`"* and *"joined by an even antipath with interior in `W`"*; the published 4.6 reads
*"with interior in `A`"* and *"with interior in `B`"*.  Since `A₁ ⊆ A` and `W ⊆ B`, the
published hypotheses are weaker, hence the published theorem is stronger.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S04

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.SkewTools Workspace.Types.SkewTools.SPGT

namespace SPGT

/-! ### Infrastructure for 4.2

None of this is in the paper.  It is the bookkeeping behind the printed phrases
*"`A₁'` is a maximal connected subset of `A₁ \ {v}`"*, *"`B₂` is still an anticomponent of
`B'`"*, *"`(A₀,B₀)` is a skew partition"* and *"`|B| − 2|B₁|` is minimum". -/

namespace Helpers42

open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Balancedness is inherited by subsets on both sides. -/
theorem balanced_mono {G : SimpleGraph V} {A B A' B' : Set V}
    (h : Workspace.Types.Core.SPGT.Balanced G A B) (hA : A' ⊆ A) (hB : B' ⊆ B) :
    Workspace.Types.Core.SPGT.Balanced G A' B' :=
  ⟨fun u v p hu hv h1 h2 h3 => h.1 u v p (hB hu) (hB hv) h1 h2 (fun x hx => hA (h3 x hx)),
   fun u v p hu hv h1 h2 h3 => h.2 u v p (hA hu) (hA hv) h1 h2 (fun x hx => hB (h3 x hx))⟩

theorem anticomplete_mono_right {G : SimpleGraph V} {S T T' : Set V}
    (h : Anticomplete G S T) (hT : T' ⊆ T) : Anticomplete G S T' :=
  fun x hx y hy => h x hx y (hT hy)

theorem anticomplete_mono_left {G : SimpleGraph V} {S S' T : Set V}
    (h : Anticomplete G S T) (hS : S' ⊆ S) : Anticomplete G S' T :=
  fun x hx y hy => h x (hS hx) y hy

/-- A nonempty set that is not connected is nonempty — the complement-free half of
`LooseSkewPartition.nonempty_of_not_anticonnected`. -/
theorem nonempty_of_not_connected {G : SimpleGraph V} {A : Set V}
    (h : ¬ ConnectedSet G A) : A.Nonempty := by
  rcases Set.eq_empty_or_nonempty A with rfl | hne
  · exact absurd (fun p _ => absurd p.2 (Set.notMem_empty _)) h
  · exact hne

/-- A component `C` of `A` is anticomplete to the rest of `A`. -/
theorem anticomplete_diff {G : SimpleGraph V} {A C : Set V}
    (hC : IsComponent G A C) : Anticomplete G C (A \ C) := by
  intro x hx y hy hadj
  obtain ⟨D, hD, hyD⟩ := ComponentsOfSetBasics.exists_isComponent_mem G A hy.1
  have hne : C ≠ D := fun he => hy.2 (he ▸ hyD)
  exact ComponentsOfSetBasics.anticomplete_of_isComponent G hC hD hne x hx y hyD hadj

/-- Any connected set is a component of itself. -/
theorem isComponent_self {G : SimpleGraph V} {C : Set V} (h : ConnectedSet G C) :
    IsComponent G C C :=
  ⟨subset_rfl, h, fun _ h1 h2 _ => Set.Subset.antisymm h2 h1⟩

/-- A component of `S` is a component of any `A = S ∪ T` with `S` anticomplete to `T`. -/
theorem isComponent_of_split {G : SimpleGraph V} {A S C T : Set V}
    (hC : IsComponent G S C) (hCne : C.Nonempty) (hA : A = S ∪ T)
    (hanti : Anticomplete G S T) : IsComponent G A C := by
  refine ⟨fun x hx => hA ▸ Or.inl (hC.1 hx), hC.2.1, ?_⟩
  intro D hCD hDA hDcon
  obtain ⟨x, hx⟩ := hCne
  have hDS : D ⊆ S :=
    StripSystemNeighbourhood.connectedSet_subset_of_anticomplete hanti hDcon
      (by rw [← hA]; exact hDA) (hCD hx) (hC.1 hx)
  exact hC.2.2 D hCD hDS hDcon

/-- A set that splits into two nonempty mutually anticomplete parts is disconnected. -/
theorem not_connectedSet_of_split {G : SimpleGraph V} {A S T : Set V}
    (hA : A = S ∪ T) (hS : S.Nonempty) (hT : T.Nonempty) (hdisj : Disjoint S T)
    (hanti : Anticomplete G S T) : ¬ ConnectedSet G A := by
  rw [hA]
  exact (Workspace.Types.AnticompleteUnionComponents.anticompleteUnionComponents
    G S T hdisj hS hT hanti).1

/-- A connected subset of `A` meeting a component `C` of `A` is contained in `C`. -/
theorem subset_component {G : SimpleGraph V} {A S C : Set V}
    (hS : ConnectedSet G S) (hSA : S ⊆ A) (hC : IsComponent G A C)
    {x : V} (hxS : x ∈ S) (hxC : x ∈ C) : S ⊆ C := by
  have hcon : ConnectedSet G (C ∪ S) :=
    ConnectedSetUnionAttach.connectedSet_union hC.2.1 hS (Or.inl ⟨x, hxC, hxS⟩)
  have heq : C ∪ S = C :=
    hC.2.2 (C ∪ S) Set.subset_union_left (Set.union_subset hC.1 hSA) hcon
  intro y hy
  have hy' : y ∈ C ∪ S := Or.inr hy
  rwa [heq] at hy'

/-- A set with at least two elements has an element different from any prescribed vertex. -/
theorem exists_ne_of_two {S : Set V} (hS : S.Nonempty)
    (htwo : ∀ x ∈ S, ∃ y ∈ S, y ≠ x) (v : V) : ∃ y ∈ S, y ≠ v := by
  obtain ⟨x, hx⟩ := hS
  by_cases hxv : x = v
  · obtain ⟨y, hy, hyx⟩ := htwo x hx
    exact ⟨y, hy, by rw [← hxv]; exact hyx⟩
  · exact ⟨x, hx, hxv⟩

/-- Every set of a `Fintype` has at most `Fintype.card V` elements. -/
theorem ncard_le_card (S : Set V) : S.ncard ≤ Fintype.card V := by
  have h := Set.ncard_le_ncard (Set.subset_univ S) Set.finite_univ
  simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using h

end Helpers42

section Main42

open Workspace.ProofLemmas
open Helpers42

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The body of the printed proof of 4.2**, in the case the paper reduces to: *"some vertex
in `B` has no neighbour in some component of `A`"*.

*"With `G` fixed, let us choose the skew partition `(A,B)` and a component `A₁` of `A` and an
anticomponent `B₁` of `B` with `|B| − 2|B₁|` minimum, such that some vertex in `B₁` (say `b₁`)
has no neighbour in `A₁`."*  Since `B₁ ⊆ B`, the integer `|B| − 2|B₁|` equals
`|B \ B₁| − |B₁|`; the natural number `|B \ B₁| + (|V(G)| − |B₁|)` differs from it by the
constant `|V(G)|`, so minimising the one minimises the other. -/
theorem key {G : SimpleGraph V} (hG : Berge G)
    (A₀ B₀ : Set V) (hAB₀ : IsSkewPartition G A₀ B₀)
    (b₀ : V) (hb₀ : b₀ ∈ B₀) (C₀ : Set V) (hC₀ : IsComponent G A₀ C₀)
    (hanti₀ : VertexAnticomplete G b₀ C₀) :
    AdmitsBalancedSkewPartition G := by
  classical
  -- the family of admissible configurations, indexed by the value of the measure
  have hex : ∃ n : ℕ, ∃ A B A₁ B₁ : Set V,
      (IsSkewPartition G A B ∧ IsComponent G A A₁ ∧ IsAnticomponent G B B₁ ∧
        ∃ b ∈ B₁, VertexAnticomplete G b A₁) ∧
      (B \ B₁).ncard + (Fintype.card V - B₁.ncard) = n := by
    obtain ⟨B₁, hB₁, hb₀B₁⟩ :=
      ComponentsOfSetBasics.exists_isComponent_mem Gᶜ B₀ hb₀
    exact ⟨_, A₀, B₀, C₀, B₁, ⟨hAB₀, hC₀, hB₁, b₀, hb₀B₁, hanti₀⟩, rfl⟩
  obtain ⟨A, B, A₁, B₁, ⟨hAB, hA₁, hB₁, b₁, hb₁, hb₁anti⟩, hmeas⟩ := Nat.find_spec hex
  have hopt : ∀ A' B' A₁' B₁' : Set V,
      (IsSkewPartition G A' B' ∧ IsComponent G A' A₁' ∧ IsAnticomponent G B' B₁' ∧
        ∃ b ∈ B₁', VertexAnticomplete G b A₁') →
      Nat.find hex ≤ (B' \ B₁').ncard + (Fintype.card V - B₁'.ncard) := by
    intro A' B' A₁' B₁' hP
    exact Nat.find_min' hex ⟨A', B', A₁', B₁', hP, rfl⟩
  -- *"By 4.1 we may assume that no `|A_i|` or `|B_j|` = 1"*
  by_cases hsing : (∃ A' : Set V, IsComponent G A A' ∧ ∃ a : V, A' = {a}) ∨
      (∃ B' : Set V, IsAnticomponent G B B' ∧ ∃ b : V, B' = {b})
  · exact thm_4_1 G hG A B hAB hsing
  obtain ⟨hsA, hsB⟩ := not_or.mp hsing
  have htwoA : ∀ A' : Set V, IsComponent G A A' → ∀ x ∈ A', ∃ y ∈ A', y ≠ x := by
    intro A' hA' x hx
    by_contra hc
    push_neg at hc
    exact hsA ⟨A', hA', x, Set.eq_singleton_iff_unique_mem.mpr ⟨hx, fun y hy => hc y hy⟩⟩
  have htwoB : ∀ B' : Set V, IsAnticomponent G B B' → ∀ x ∈ B', ∃ y ∈ B', y ≠ x := by
    intro B' hB' x hx
    by_contra hc
    push_neg at hc
    exact hsB ⟨B', hB', x, Set.eq_singleton_iff_unique_mem.mpr ⟨hx, fun y hy => hc y hy⟩⟩
  -- basic bookkeeping about the chosen partition
  have hAne : A.Nonempty := nonempty_of_not_connected hAB.2.2.1
  have hBne : B.Nonempty := LooseSkewPartition.nonempty_of_not_anticonnected hAB.2.2.2
  have hnotB : ∀ x ∈ A, x ∉ B := fun x hx => Set.disjoint_left.mp hAB.2.1 hx
  have hnotA : ∀ x ∈ B, x ∉ A := fun x hx hxA => hnotB x hxA hx
  have hA₁ne : A₁.Nonempty := ComponentsOfSetBasics.nonempty_of_isComponent G hAne hA₁
  have hB₁ne : B₁.Nonempty := ComponentsOfSetBasics.nonempty_of_isComponent Gᶜ hBne hB₁
  have hb₁B : b₁ ∈ B := hB₁.1 hb₁
  -- distinct anticomponents of `B` are complete to one another in `G`
  have hcompl : ∀ P Q : Set V, IsAnticomponent G B P → IsAnticomponent G B Q → P ≠ Q →
      ∀ x ∈ P, ∀ y ∈ Q, G.Adj x y := by
    intro P Q hP hQ hPQ x hx y hy
    have hxy : x ≠ y := fun he =>
      (Set.disjoint_left.mp (ComponentsOfSetBasics.disjoint_of_isComponent Gᶜ hP hQ hPQ) hx)
        (he ▸ hy)
    by_contra hg
    exact ComponentsOfSetBasics.anticomplete_of_isComponent Gᶜ hP hQ hPQ x hx y hy ⟨hxy, hg⟩
  ------------------------------------------------------------------
  -- (1), second claim: *"every vertex in `B \ B₁` has a neighbour in `A₁`"*
  ------------------------------------------------------------------
  have claim1b : ∀ v : V, v ∈ B → v ∉ B₁ → ∃ a ∈ A₁, G.Adj v a := by
    intro v hvB hvB₁
    by_contra hcon
    push_neg at hcon
    -- *"assume that some vertex `v ∈ B₂` say has no neighbour in `A₁`"*
    obtain ⟨B₂, hB₂, hvB₂⟩ := ComponentsOfSetBasics.exists_isComponent_mem Gᶜ B hvB
    have hB₂ne₁ : B₂ ≠ B₁ := fun he => hvB₁ (he ▸ hvB₂)
    -- *"since `|B₂| ≥ 2`"*
    obtain ⟨w, hwB₂, hwv⟩ := exists_ne_of_two
      (ComponentsOfSetBasics.nonempty_of_isComponent Gᶜ hBne hB₂) (htwoB B₂ hB₂) v
    have hvA : v ∉ A := hnotA v hvB
    have hwB : w ∈ B := hB₂.1 hwB₂
    have hwB₁ : w ∉ B₁ := fun hw =>
      (Set.disjoint_left.mp
        (ComponentsOfSetBasics.disjoint_of_isComponent Gᶜ hB₂ hB₁ hB₂ne₁) hwB₂) hw
    -- the new pair `(A ∪ {v}, B \ {v})`
    have hsplitA : A ∪ {v} = A₁ ∪ ((A \ A₁) ∪ {v}) := by
      ext x
      constructor
      · rintro (hx | hx)
        · by_cases h : x ∈ A₁
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨hx, h⟩)
        · exact Or.inr (Or.inr hx)
      · rintro (hx | hx | hx)
        · exact Or.inl (hA₁.1 hx)
        · exact Or.inl hx.1
        · exact Or.inr hx
    have hantiA : Anticomplete G A₁ ((A \ A₁) ∪ {v}) := by
      intro x hx y hy
      rcases hy with hy | hy
      · exact anticomplete_diff hA₁ x hx y hy
      · intro hadj
        exact hcon x hx (by rw [(hy : y = v)] at hadj; exact hadj.symm)
    have hAdisj : Disjoint A₁ ((A \ A₁) ∪ {v}) := by
      refine Set.disjoint_left.mpr ?_
      rintro a ha (hb | hb)
      · exact hb.2 ha
      · exact hvA (hA₁.1 ((hb : a = v) ▸ ha))
    have hAcomp : IsComponent G (A ∪ {v}) A₁ :=
      isComponent_of_split (isComponent_self hA₁.2.1) hA₁ne hsplitA hantiA
    have hAnc : ¬ ConnectedSet G (A ∪ {v}) :=
      not_connectedSet_of_split hsplitA hA₁ne ⟨v, Or.inr rfl⟩ hAdisj hantiA
    have hB₁subv : B₁ ⊆ B \ {v} := fun x hx => ⟨hB₁.1 hx, fun hxv => hvB₁ ((hxv : x = v) ▸ hx)⟩
    have hsplitB : B \ {v} = B₁ ∪ ((B \ {v}) \ B₁) := by
      ext x
      constructor
      · intro hx
        by_cases h : x ∈ B₁
        · exact Or.inl h
        · exact Or.inr ⟨hx, h⟩
      · rintro (hx | hx)
        · exact hB₁subv hx
        · exact hx.1
    have hantiB : Anticomplete Gᶜ B₁ ((B \ {v}) \ B₁) :=
      anticomplete_mono_right (anticomplete_diff hB₁) (fun x hx => ⟨hx.1.1, hx.2⟩)
    have hBdisj : Disjoint B₁ ((B \ {v}) \ B₁) :=
      Set.disjoint_left.mpr (fun a ha hb => hb.2 ha)
    have hBcomp : IsAnticomponent G (B \ {v}) B₁ :=
      isComponent_of_split (isComponent_self hB₁.2.1) hB₁ne hsplitB hantiB
    have hBnc : ¬ AnticonnectedSet G (B \ {v}) :=
      not_connectedSet_of_split hsplitB hB₁ne ⟨w, ⟨hwB, hwv⟩, hwB₁⟩ hBdisj hantiB
    have hskew : IsSkewPartition G (A ∪ {v}) (B \ {v}) := by
      refine ⟨?_, ?_, hAnc, hBnc⟩
      · apply Set.eq_univ_of_forall
        intro x
        by_cases hx : x = v
        · exact Or.inl (Or.inr hx)
        · have hxAB : x ∈ A ∪ B := by rw [hAB.1]; trivial
          rcases hxAB with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr ⟨h, hx⟩
      · refine Set.disjoint_left.mpr ?_
        rintro a (ha | ha) hb
        · exact hnotB a ha hb.1
        · exact hb.2 ha
    -- the measure strictly decreases
    have hdiff : (B \ {v}) \ B₁ = (B \ B₁) \ {v} := by
      ext x
      exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩⟩
    have hvmem : v ∈ B \ B₁ := ⟨hvB, hvB₁⟩
    have hcard : ((B \ {v}) \ B₁).ncard = (B \ B₁).ncard - 1 := by
      rw [hdiff]; exact Set.ncard_diff_singleton_of_mem hvmem
    have hpos : 1 ≤ (B \ B₁).ncard := by
      have h := (Set.ncard_pos (s := B \ B₁) (Set.toFinite _)).mpr ⟨v, hvmem⟩
      omega
    have hle := hopt (A ∪ {v}) (B \ {v}) A₁ B₁ ⟨hskew, hAcomp, hBcomp, b₁, hb₁, hb₁anti⟩
    rw [hcard] at hle
    omega
  ------------------------------------------------------------------
  -- (1), first claim: *"no vertex in `A` is `B_j`-complete and not `B₁`-complete"*
  ------------------------------------------------------------------
  have claim1a : ∀ v : V, v ∈ A → ∀ B₂ : Set V, IsAnticomponent G B B₂ → B₂ ≠ B₁ →
      VertexComplete G v B₂ → VertexComplete G v B₁ := by
    intro v hvA B₂ hB₂ hB₂ne₁ hcomp
    by_contra hncomp
    -- *"since `v` is not `B₁`-complete, there is an anticomponent of `B'` including
    --  `B₁ ∪ {v}`"*
    rw [VertexComplete] at hncomp
    push_neg at hncomp
    obtain ⟨c, hc, hvc⟩ := hncomp
    have hvB : v ∉ B := hnotB v hvA
    have hB₂ne : B₂.Nonempty := ComponentsOfSetBasics.nonempty_of_isComponent Gᶜ hBne hB₂
    -- *"let `A₁'` be a maximal connected subset of `A₁ \ {v}`"*
    obtain ⟨z, hz⟩ : (A₁ \ {v}).Nonempty := by
      obtain ⟨y, hy, hyv⟩ := exists_ne_of_two hA₁ne (htwoA A₁ hA₁) v
      exact ⟨y, hy, hyv⟩
    obtain ⟨A₁', hA₁', hzA₁'⟩ :=
      ComponentsOfSetBasics.exists_isComponent_mem G (A₁ \ {v}) hz
    have hA₁'ne : A₁'.Nonempty := ⟨z, hzA₁'⟩
    have hA₁'sub : A₁' ⊆ A₁ := fun x hx => (hA₁'.1 hx).1
    have hsplitA : A \ {v} = (A₁ \ {v}) ∪ ((A \ A₁) \ {v}) := by
      ext x
      constructor
      · intro hx
        by_cases h : x ∈ A₁
        · exact Or.inl ⟨h, hx.2⟩
        · exact Or.inr ⟨⟨hx.1, h⟩, hx.2⟩
      · rintro (hx | hx)
        · exact ⟨hA₁.1 hx.1, hx.2⟩
        · exact ⟨hx.1.1, hx.2⟩
    have hantiA : Anticomplete G (A₁ \ {v}) ((A \ A₁) \ {v}) :=
      anticomplete_mono_left
        (anticomplete_mono_right (anticomplete_diff hA₁) (fun x hx => hx.1))
        (fun x hx => hx.1)
    have hAcomp : IsComponent G (A \ {v}) A₁' :=
      isComponent_of_split hA₁' hA₁'ne hsplitA hantiA
    -- the other part of `A \ {v}` is nonempty: `A` has a second component, of size `≥ 2`
    obtain ⟨P, Q, hP, hQ, hPQ⟩ :=
      ComponentsOfSetBasics.exists_two_isComponent G hAne hAB.2.2.1
    obtain ⟨A₂, hA₂, hA₂ne₁⟩ : ∃ A₂ : Set V, IsComponent G A A₂ ∧ A₂ ≠ A₁ := by
      by_cases hPA : P = A₁
      · exact ⟨Q, hQ, fun he => hPQ (hPA.trans he.symm)⟩
      · exact ⟨P, hP, hPA⟩
    obtain ⟨y, hyA₂, hyv⟩ := exists_ne_of_two
      (ComponentsOfSetBasics.nonempty_of_isComponent G hAne hA₂) (htwoA A₂ hA₂) v
    have hyT : y ∈ (A \ A₁) \ {v} :=
      ⟨⟨hA₂.1 hyA₂, fun hy₁ =>
        (Set.disjoint_left.mp
          (ComponentsOfSetBasics.disjoint_of_isComponent G hA₂ hA₁ hA₂ne₁) hyA₂) hy₁⟩, hyv⟩
    have hAdisj : Disjoint (A₁ \ {v}) ((A \ A₁) \ {v}) :=
      Set.disjoint_left.mpr (fun a ha hb => hb.1.2 ha.1)
    have hAnc : ¬ ConnectedSet G (A \ {v}) :=
      not_connectedSet_of_split hsplitA ⟨z, hz⟩ ⟨y, hyT⟩ hAdisj hantiA
    -- *"then `B₂` is still an anticomponent of `B'`"*
    have hsplitB : B ∪ {v} = B₂ ∪ ((B ∪ {v}) \ B₂) := by
      ext x
      constructor
      · intro hx
        by_cases h : x ∈ B₂
        · exact Or.inl h
        · exact Or.inr ⟨hx, h⟩
      · rintro (hx | hx)
        · exact Or.inl (hB₂.1 hx)
        · exact hx.1
    have hantiB : Anticomplete Gᶜ B₂ ((B ∪ {v}) \ B₂) := by
      intro x hx y hy
      rcases hy.1 with hyB | hyv'
      · exact anticomplete_diff hB₂ x hx y ⟨hyB, hy.2⟩
      · intro hadj
        exact ((SimpleGraph.compl_adj G x y).mp hadj).2
          (((hyv' : y = v) ▸ (hcomp x hx)).symm)
    have hBdisj : Disjoint B₂ ((B ∪ {v}) \ B₂) :=
      Set.disjoint_left.mpr (fun a ha hb => hb.2 ha)
    have hB₁B₂ : Disjoint B₁ B₂ :=
      ComponentsOfSetBasics.disjoint_of_isComponent Gᶜ hB₁ hB₂ (fun he => hB₂ne₁ he.symm)
    obtain ⟨b, hbB₁⟩ := hB₁ne
    have hbT : b ∈ (B ∪ {v}) \ B₂ :=
      ⟨Or.inl (hB₁.1 hbB₁), fun hb => (Set.disjoint_left.mp hB₁B₂ hbB₁) hb⟩
    have hBnc : ¬ AnticonnectedSet G (B ∪ {v}) :=
      not_connectedSet_of_split hsplitB hB₂ne ⟨b, hbT⟩ hBdisj hantiB
    -- the new anticomponent containing `B₁ ∪ {v}`
    obtain ⟨B₁'', hB₁'', hvB₁''⟩ :=
      ComponentsOfSetBasics.exists_isComponent_mem Gᶜ (B ∪ {v}) (Or.inr rfl)
    have hconn : ConnectedSet Gᶜ (B₁ ∪ {v}) :=
      ConnectedSetUnionAttach.connectedSet_union_singleton hB₁.2.1
        ⟨c, hc, ⟨fun he => hvB (he ▸ hB₁.1 hc), hvc⟩⟩
    have hincl : B₁ ∪ {v} ⊆ B₁'' :=
      subset_component hconn
        (Set.union_subset (fun x hx => Or.inl (hB₁.1 hx)) (fun x hx => Or.inr hx))
        hB₁'' (Or.inr rfl) hvB₁''
    have hB₁sub'' : B₁ ⊆ B₁'' := fun x hx => hincl (Or.inl hx)
    -- the new pair is a skew partition
    have hskew : IsSkewPartition G (A \ {v}) (B ∪ {v}) := by
      refine ⟨?_, ?_, hAnc, hBnc⟩
      · apply Set.eq_univ_of_forall
        intro x
        by_cases hx : x = v
        · exact Or.inr (Or.inr hx)
        · have hxAB : x ∈ A ∪ B := by rw [hAB.1]; trivial
          rcases hxAB with h | h
          · exact Or.inl ⟨h, hx⟩
          · exact Or.inr (Or.inl h)
      · refine Set.disjoint_left.mpr ?_
        rintro a ha (hb | hb)
        · exact hnotB a ha.1 hb
        · exact ha.2 hb
    -- the measure strictly decreases
    have hvB₁ : v ∉ B₁ := fun hv => hvB (hB₁.1 hv)
    have hcard1 : B₁.ncard + 1 ≤ B₁''.ncard := by
      have h1 : (insert v B₁).ncard = B₁.ncard + 1 :=
        Set.ncard_insert_of_notMem hvB₁ (Set.toFinite _)
      have h2 : insert v B₁ ⊆ B₁'' := by
        intro x hx
        rcases hx with hx | hx
        · exact hincl (Or.inr hx)
        · exact hB₁sub'' hx
      have := Set.ncard_le_ncard h2 (Set.toFinite _)
      omega
    have hcard2 : ((B ∪ {v}) \ B₁'').ncard ≤ (B \ B₁).ncard := by
      refine Set.ncard_le_ncard ?_ (Set.toFinite _)
      rintro x ⟨hx1, hx2⟩
      have hxv : x ≠ v := fun he => hx2 (he ▸ hvB₁'')
      rcases hx1 with h | h
      · exact ⟨h, fun hb => hx2 (hB₁sub'' hb)⟩
      · exact absurd (h : x = v) hxv
    have hcard3 : B₁''.ncard ≤ Fintype.card V := ncard_le_card B₁''
    have hle := hopt (A \ {v}) (B ∪ {v}) A₁' B₁''
      ⟨hskew, hAcomp, hB₁'', b₁, hB₁sub'' hb₁, fun x hx => hb₁anti x (hA₁'sub hx)⟩
    omega
  ------------------------------------------------------------------
  -- *"By 2.6, the pair `(A₁,B_j)` is balanced, for `2 ≤ j ≤ n` …"*
  ------------------------------------------------------------------
  -- a second anticomponent `B₂` of `B`
  obtain ⟨P, Q, hP, hQ, hPQ⟩ :=
    ComponentsOfSetBasics.exists_two_isComponent Gᶜ hBne hAB.2.2.2
  obtain ⟨B₂, hB₂, hB₂ne₁⟩ : ∃ B₂ : Set V, IsAnticomponent G B B₂ ∧ B₂ ≠ B₁ := by
    by_cases hPB : P = B₁
    · exact ⟨Q, hQ, fun he => hPQ (hPB.trans he.symm)⟩
    · exact ⟨P, hP, hPB⟩
  -- *"By 2.6, `(A₁,B_j)` is balanced … since `b₁` is complete to `B_j` and has no neighbours
  --   in `A₁`"*
  have stepA : ∀ Bj : Set V, IsAnticomponent G B Bj → Bj ≠ B₁ →
      Workspace.Types.Core.SPGT.Balanced G A₁ Bj := by
    intro Bj hBj hBjne
    have hdisj : Disjoint A₁ Bj :=
      Set.disjoint_left.mpr (fun a ha hb => hnotB a (hA₁.1 ha) (hBj.1 hb))
    have hb₁Bj : b₁ ∉ Bj := fun hb =>
      (Set.disjoint_left.mp
        (ComponentsOfSetBasics.disjoint_of_isComponent Gᶜ hB₁ hBj
          (fun he => hBjne he.symm)) hb₁) hb
    refine Workspace.Statements.S02.SPGT.thm_2_6 G hG A₁ Bj hdisj b₁ ?_ ?_ hb₁anti
    · rintro (h | h)
      · exact hnotA b₁ hb₁B (hA₁.1 h)
      · exact hb₁Bj h
    · exact LooseSkewPartition.vertexComplete_of_notMem_anticomponent hBj hb₁B hb₁Bj
  -- *"By (1) and 2.7.1, it follows that `(A_i,B_j)` is balanced"*
  have stepB : ∀ Ai Bj : Set V, IsComponent G A Ai → IsAnticomponent G B Bj → Bj ≠ B₁ →
      Workspace.Types.Core.SPGT.Balanced G Ai Bj := by
    intro Ai Bj hAi hBj hBjne
    by_cases hAiA₁ : Ai = A₁
    · exact hAiA₁ ▸ stepA Bj hBj hBjne
    have hsub : Ai ⊆ (A₁ ∪ Bj)ᶜ := by
      intro x hx
      rintro (h | h)
      · exact (Set.disjoint_left.mp
          (ComponentsOfSetBasics.disjoint_of_isComponent G hAi hA₁ hAiA₁) hx) h
      · exact hnotB x (hAi.1 hx) (hBj.1 h)
    refine (Workspace.Statements.S02.SPGT.thm_2_7 G hG A₁ Bj (stepA Bj hBj hBjne) Ai hsub).1
      hA₁.2.1 ?_ ?_
    · intro b hb
      refine claim1b b (hBj.1 hb) (fun hbB₁ => ?_)
      exact (Set.disjoint_left.mp
        (ComponentsOfSetBasics.disjoint_of_isComponent Gᶜ hBj hB₁ hBjne) hb) hbB₁
    · exact fun x hx => ComponentsOfSetBasics.anticomplete_of_isComponent G hA₁ hAi
        (fun he => hAiA₁ he.symm) x hx
  -- *"It remains to check all the pairs `(A_i,B₁)`"*
  have stepC : ∀ Ai : Set V, IsComponent G A Ai →
      Workspace.Types.Core.SPGT.Balanced G Ai B₁ := by
    intro Ai hAi
    have hbal2 : Workspace.Types.Core.SPGT.Balanced G
        {x : V | x ∈ Ai ∧ ¬ VertexComplete G x B₁} B₂ :=
      balanced_mono (stepB Ai B₂ hAi hB₂ hB₂ne₁) (fun x hx => hx.1) subset_rfl
    have hsub : B₁ ⊆ ({x : V | x ∈ Ai ∧ ¬ VertexComplete G x B₁} ∪ B₂)ᶜ := by
      intro x hx
      rintro (h | h)
      · exact hnotA x (hB₁.1 hx) (hAi.1 h.1)
      · exact (Set.disjoint_left.mp
          (ComponentsOfSetBasics.disjoint_of_isComponent Gᶜ hB₁ hB₂
            (fun he => hB₂ne₁ he.symm)) hx) h
    have hnc : ∀ a ∈ {x : V | x ∈ Ai ∧ ¬ VertexComplete G x B₁}, ¬ VertexComplete G a B₂ :=
      fun a ha hcomp => ha.2 (claim1a a (hAi.1 ha.1) B₂ hB₂ hB₂ne₁ hcomp)
    have hcomplete : Complete G B₂ B₁ := fun x hx y hy => hcompl B₂ B₁ hB₂ hB₁ hB₂ne₁ x hx y hy
    exact BalancedRestrictNonComplete.balanced_of_notComplete
      ((Workspace.Statements.S02.SPGT.thm_2_7 G hG
        {x : V | x ∈ Ai ∧ ¬ VertexComplete G x B₁} B₂ hbal2 B₁ hsub).2
        hB₂.2.1 hnc hcomplete)
  -- *"This proves that `(A,B)` is balanced"*
  refine ⟨A, B, hAB, BalancedComponentwise.balanced_of_components hAne hBne ?_⟩
  intro A' B' hA' hB'
  by_cases hB'B₁ : B' = B₁
  · exact hB'B₁ ▸ stepC A' hA'
  · exact stepB A' B' hA' hB' hB'B₁

end Main42

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **4.2** (printed p. 15)

PAPER: *"If `G` is Berge, and admits a loose skew partition, then it admits a balanced skew
partition."*

*Loose* is the printed-p.-15 notion: *"a skew partition `(A,B)` of `G` is loose if either some
vertex in `B` has no neighbour in some component of `A`, or some vertex in `A` is complete to
some anticomponent of `B`"*; `AdmitsLooseSkewPartition G` says some skew partition of `G` is
loose. -/
theorem thm_4_2 (G : SimpleGraph V) (hG : Berge G)
    (hloose : AdmitsLooseSkewPartition G) :
    AdmitsBalancedSkewPartition G := by
  obtain ⟨A, B, hAB, hcase⟩ := hloose
  rcases hcase with ⟨b, hb, A', hA', hanti⟩ | ⟨a, ha, B', hB', hcomp⟩
  · exact key hG A B hAB b hb A' hA' hanti
  · -- *"By taking complements if necessary, we may assume that some vertex in `B` has no
    --  neighbour in some component of `A`."*
    refine Workspace.ProofLemmas.ClassLemmas.admitsBalancedSkewPartition_compl.mp
      (key (Workspace.ProofLemmas.HoleBasics.berge_compl.mpr hG) B A
        (Workspace.ProofLemmas.ClassLemmas.isSkewPartition_compl.mpr hAB) a ha B' hB' ?_)
    intro x hx hadj
    exact ((SimpleGraph.compl_adj G a x).mp hadj).2 (hcomp x hx)


end SPGT

end Workspace.Statements.S04
