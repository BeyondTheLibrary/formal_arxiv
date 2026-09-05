import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.SelectedStripSeparationData
import Workspace.Statements.S04.Thm_4_1

set_option autoImplicit false

namespace Workspace.ProofLemmas.IntersectingStripEndsGiveBalancedSkewPartition

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

/-! ### Bookkeeping

None of this is in the paper; it is what the printed phrase *"it follows that
`((B \ (B₁ ∪ B₂)) ∪ (A \ {a}), B₁ ∪ B₂ ∪ {a})` is a skew partition of `G`"* and
*"`{a}` is an anticomponent of `B₁ ∪ B₂ ∪ {a}`"* stand for. -/

section Helpers

variable {V : Type*}

/-- Along a walk inside `X`, membership in a set `P` which is "closed under the
edges of `G|X`" is invariant. -/
private theorem reach_iff {G : SimpleGraph V} {X P : Set V}
    (hsep : ∀ p, p ∈ X → ∀ q, q ∈ X → G.Adj p q → (p ∈ P ↔ q ∈ P))
    {u v : ↥X} (h : (G.induce X).Reachable u v) : ((u : V) ∈ P ↔ (v : V) ∈ P) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact Iff.rfl
  | @cons a b c hadj w ih => exact (hsep a.1 a.2 b.1 b.2 hadj).trans ih

/-- If `X` splits into two parts with no edges of `G` between them and both parts
are inhabited, then `X` is not connected. -/
private theorem not_connectedSet_split {G : SimpleGraph V} {X P : Set V}
    (hsep : ∀ p, p ∈ X → ∀ q, q ∈ X → G.Adj p q → (p ∈ P ↔ q ∈ P))
    {x y : V} (hx : x ∈ X) (hy : y ∈ X) (hxP : x ∈ P) (hyP : y ∉ P) :
    ¬ ConnectedSet G X := fun h =>
  hyP ((reach_iff hsep (h ⟨x, hx⟩ ⟨y, hy⟩)).mp hxP)

/-- A vertex of `Y` with no `G`-neighbour in `Y` is a component of `Y` all by
itself. -/
private theorem isComponent_singleton_of_isolated {G : SimpleGraph V} {Y : Set V}
    {a : V} (haY : a ∈ Y) (hiso : ∀ z ∈ Y, ¬ G.Adj a z) :
    IsComponent G Y ({a} : Set V) := by
  have hconn : ∀ (W : Set V), a ∈ W → W ⊆ Y →
      ∀ p, p ∈ W → ∀ q, q ∈ W → G.Adj p q → (p ∈ ({a} : Set V) ↔ q ∈ ({a} : Set V)) := by
    intro W _ hWY p hp q hq hadj
    constructor
    · intro hpa
      exact absurd (show G.Adj a q by rw [← show p = a from hpa]; exact hadj) (hiso q (hWY hq))
    · intro hqa
      exact absurd (show G.Adj a p by rw [← show q = a from hqa]; exact hadj.symm)
        (hiso p (hWY hp))
  refine ⟨by simpa using haY, ?_, ?_⟩
  · intro u v
    have huv : u = v := Subtype.ext (by
      rw [show (u : V) = a from u.2, show (v : V) = a from v.2])
    rw [huv]
  · intro D haD hDY hDconn
    apply Set.eq_of_subset_of_subset _ haD
    intro z hz
    have haD' : a ∈ D := haD rfl
    have := reach_iff (P := ({a} : Set V)) (hconn D haD' hDY)
      (hDconn ⟨a, haD'⟩ ⟨z, hz⟩)
    exact this.mp rfl

end Helpers

/-- **8.6 endgame, B10** (printed p. 46).

Intersecting end-sets in the selected-strip separation yield a balanced skew
partition. -/
theorem intersectingStripEndsGiveBalancedSkewPartition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G) (A B A₁ A₂ B₁ B₂ : Set V)
    (hpartition : A ∪ B = Set.univ ∧ Disjoint A B)
    (hA₁ : A₁.Nonempty ∧ A₁ ⊆ A)
    (hA₂ : A₂.Nonempty ∧ A₂ ⊆ A)
    (hB₁ : B₁.Nonempty ∧ B₁ ⊆ B)
    (hB₂ : B₂.Nonempty ∧ B₂ ⊆ B)
    (hcross : ∀ a ∈ A, ∀ b ∈ B,
      G.Adj a b ↔ ((a ∈ A₁ ∧ b ∈ B₁) ∨ (a ∈ A₂ ∧ b ∈ B₂)))
    (hAcard : 2 ≤ A.ncard)
    (hBmiddle : (B \ (B₁ ∪ B₂)).Nonempty)
    (hintersect : (A₁ ∩ A₂).Nonempty) :
    AdmitsBalancedSkewPartition G := by
  obtain ⟨hunion, hdisj⟩ := hpartition
  -- "there exists `a ∈ A₁ ∩ A₂`"
  obtain ⟨a, haA₁, haA₂⟩ := hintersect
  have haA : a ∈ A := hA₁.2 haA₁
  -- "`a` is complete to `B₁ ∪ B₂`"
  have hacomp : ∀ b ∈ B₁ ∪ B₂, G.Adj a b := by
    rintro b (hb | hb)
    · exact (hcross a haA b (hB₁.2 hb)).mpr (Or.inl ⟨haA₁, hb⟩)
    · exact (hcross a haA b (hB₂.2 hb)).mpr (Or.inr ⟨haA₂, hb⟩)
  have hBB : B₁ ∪ B₂ ⊆ B := Set.union_subset hB₁.2 hB₂.2
  have haBB : a ∉ B₁ ∪ B₂ := fun h => (Set.disjoint_left.mp hdisj haA) (hBB h)
  -- "since `|A| ≥ 2`": there is a second vertex of `A`
  obtain ⟨y, hyA, hya⟩ : ∃ y, y ∈ A ∧ y ≠ a := by
    by_contra hcon
    push_neg at hcon
    have hsub : A ⊆ ({a} : Set V) := fun z hz => by
      simpa using hcon z hz
    have hle : A.ncard ≤ ({a} : Set V).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton] at hle
    omega
  obtain ⟨x, hxB, hxBB⟩ := hBmiddle
  -- The printed partition
  set X : Set V := (B \ (B₁ ∪ B₂)) ∪ (A \ ({a} : Set V)) with hXdef
  set Y : Set V := (B₁ ∪ B₂) ∪ ({a} : Set V) with hYdef
  -- `(X, Y)` is a partition of `V(G)`
  have hXY : X ∪ Y = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    have hv : v ∈ A ∪ B := by rw [hunion]; trivial
    rcases hv with hv | hv
    · by_cases hva : v = a
      · exact Or.inr (Or.inr (by simpa using hva))
      · exact Or.inl (Or.inr ⟨hv, by simpa using hva⟩)
    · by_cases hvB : v ∈ B₁ ∪ B₂
      · exact Or.inr (Or.inl hvB)
      · exact Or.inl (Or.inl ⟨hv, hvB⟩)
  have hXYdisj : Disjoint X Y := by
    rw [Set.disjoint_left]
    rintro v (⟨hvB, hvBB⟩ | ⟨hvA, hva⟩) hvY
    · rcases hvY with h | h
      · exact hvBB h
      · exact (Set.disjoint_left.mp hdisj (show v ∈ A by rw [show v = a from h]; exact haA)) hvB
    · rcases hvY with h | h
      · exact (Set.disjoint_left.mp hdisj hvA) (hBB h)
      · exact hva h
  -- `X` is not connected: no edge joins `B \ (B₁ ∪ B₂)` to `A \ {a}`
  have hXnc : ¬ ConnectedSet G X := by
    refine not_connectedSet_split (P := B \ (B₁ ∪ B₂))
      (x := x) (y := y) ?_ (Or.inl ⟨hxB, hxBB⟩) (Or.inr ⟨hyA, by simpa using hya⟩)
      ⟨hxB, hxBB⟩ (fun h => (Set.disjoint_left.mp hdisj hyA) h.1)
    have hno : ∀ p, p ∈ B \ (B₁ ∪ B₂) → ∀ q, q ∈ A \ ({a} : Set V) → ¬ G.Adj p q := by
      rintro p ⟨hpB, hpBB⟩ q ⟨hqA, -⟩ hadj
      rcases (hcross q hqA p hpB).mp hadj.symm with ⟨-, h⟩ | ⟨-, h⟩
      · exact hpBB (Or.inl h)
      · exact hpBB (Or.inr h)
    rintro p hp q hq hadj
    constructor
    · intro hpP
      by_contra hqP
      have hqQ : q ∈ A \ ({a} : Set V) := by rcases hq with h | h; · exact absurd h hqP
                                             · exact h
      exact hno p hpP q hqQ hadj
    · intro hqP
      by_contra hpP
      have hpQ : p ∈ A \ ({a} : Set V) := by rcases hp with h | h; · exact absurd h hpP
                                             · exact h
      exact hno q hqP p hpQ hadj.symm
  -- `Y` is not anticonnected: `a` is `G`-complete to `B₁ ∪ B₂`
  have haiso : ∀ z ∈ Y, ¬ Gᶜ.Adj a z := by
    rintro z (hz | hz) hadj
    · exact ((SimpleGraph.compl_adj G a z).mp hadj).2 (hacomp z hz)
    · exact hadj.ne (show a = z from (show z = a from hz).symm)
  obtain ⟨b₀, hb₀⟩ := hB₁.1
  have hYnac : ¬ AnticonnectedSet G Y := by
    refine not_connectedSet_split (G := Gᶜ) (P := ({a} : Set V))
      (x := a) (y := b₀) ?_ (Or.inr rfl) (Or.inl (Or.inl hb₀)) rfl
      (fun h => haBB (by rw [show b₀ = a from h] at hb₀; exact Or.inl hb₀))
    intro p hp q hq hadj
    constructor
    · intro hpa
      exact absurd (show Gᶜ.Adj a q by rw [← show p = a from hpa]; exact hadj) (haiso q hq)
    · intro hqa
      exact absurd (show Gᶜ.Adj a p by rw [← show q = a from hqa]; exact hadj.symm) (haiso p hp)
  -- "`{a}` is an anticomponent of `B₁ ∪ B₂ ∪ {a}`; 4.1 implies …"
  refine Workspace.Statements.S04.SPGT.thm_4_1 G hG X Y ⟨hXY, hXYdisj, hXnc, hYnac⟩
    (Or.inr ⟨({a} : Set V), ?_, a, rfl⟩)
  exact isComponent_singleton_of_isolated (G := Gᶜ) (Or.inr rfl) haiso

end Workspace.ProofLemmas.IntersectingStripEndsGiveBalancedSkewPartition
