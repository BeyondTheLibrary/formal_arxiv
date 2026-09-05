import Mathlib
import Workspace.Types.Core
import Workspace.Types.Knots
import Workspace.ProofLemmas.PathBasics

/-!
# A twist plus four rungs is a knot

Inside the printed proof of **9.4** (published p. 51) the authors write, three separate times
and always without comment:

PAPER: *"By reversing `S₂` we may assume that `S₁` and `S₂` agree on `T₁`; and we may assume
they disagree on `T₂`.  Let `a₂-P₂-b₂` be any `S₂`-rung, and `x₂-Q₂-y₂` any `T₂`-antirung.
**Then `(P₁, P₂, Q₁, Q₂)` is a knot** …"*

The same step is used again in claim (2) of 9.4 (*"But then `(P₁, P₂, Q₁, Q₂)` is a knot"*), in
the final paragraph of 9.4 (*"Then `(P₁, P₂, Q₁, Q₂)` is a knot, with union `K` say"*), in 9.5,
and in claim (3) of the proof of 9.6.  This module turns that unremarked step into a theorem.

Nothing else is proved here; in particular 9.1/9.3 (which the paper invokes *after* producing
the knot) are not touched.

## Contents

* `isKnot_of_parallel_config` — the **oriented case**: `S₁, S₂` both parallel to `T₁`, `S₁`
  parallel and `S₂` **co**-parallel to `T₂`.  This is the configuration the paper normalises to
  by *"reversing `S₂`"*, and it is exactly the pattern `IsKnot` demands, whose fourth
  edge-clause (`V(P₂)` versus `{x₂, y₂}`) is the twisted one.
* `exists_knot_of_twist` — the form a striation hands you: a twist inside a striation gives a
  knot on any choice of rungs and antirungs, after possibly reversing some of the four lists.

## Why reversing suffices, and why `P₁` is never reversed

Write `b(S, T) ∈ {∥, co}` for the four relations `(S₁,T₁), (S₁,T₂), (S₂,T₁), (S₂,T₂)`.
Reversing one of the four strips flips exactly two of the four bits — reversing `S₂` flips
`b(S₂,T₁)` and `b(S₂,T₂)`, reversing `T₁` flips `b(S₁,T₁)` and `b(S₂,T₁)`, and so on.  So the
parity of the number of `co` bits is invariant.  `IsTwist` says the two strips agree on one
antistrip (`0` co-bits in that column, or `2`) and disagree on the other (`1`), hence a twist
always has **odd** parity, and the target pattern `(∥, ∥, ∥, co)` also has odd parity.

Consequently the following greedy normalisation always succeeds, and never has to touch `S₁`
or `P₁`:

* reverse `T₁` (and `Q₁`) if `b(S₁,T₁) = co`;
* then reverse `T₂` (and `Q₂`) if `b(S₁,T₂) = co`;
* then reverse `S₂` (and `P₂`) if `b(S₂,T₁) = co`.

After the three steps the first three bits are `∥`, and odd parity forces the fourth to be
`co`.  This also means the exchange of `(Q₁, x₁, y₁)` with `(Q₂, x₂, y₂)` is never needed —
which matters, because `IsKnot` is **not** symmetric in `Q₁, Q₂`: its twisted clause is pinned
at the pair `(P₂, Q₂)`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.KnotFromTwist

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.PathBasics

variable {V : Type*}

/-! ### Symmetry of `Complete` and `Anticomplete`

The paper uses these silently (*"`Sᵢ` is anticomplete to `Sᵢ'`"* carries no order).  A striation
only records them for `i < i'`, so both directions are needed. -/

private theorem complete_symm {G : SimpleGraph V} {X Y : Set V} (h : Complete G X Y) :
    Complete G Y X := fun y hy x hx => (h x hx y hy).symm

private theorem anticomplete_symm {G : SimpleGraph V} {X Y : Set V} (h : Anticomplete G X Y) :
    Anticomplete G Y X := fun y hy x hx hadj => h x hx y hy hadj.symm

/-! ### Membership in the tail of a repetition-free list

`PathBasics.mem_dropLast_iff` is the `dropLast` half; this is the `tail` half. -/

private theorem mem_tail_iff_of_nodup {l : List V} (hnd : l.Nodup) {x u : V}
    (hh : l.head? = some u) : x ∈ l.tail ↔ (x ∈ l ∧ x ≠ u) := by
  cases l with
  | nil => simp at hh
  | cons a t =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    rw [List.nodup_cons] at hnd
    simp only [List.tail_cons, List.mem_cons]
    constructor
    · intro hx
      exact ⟨Or.inr hx, fun h => hnd.1 (h ▸ hx)⟩
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd h1 h2
      · exact h1

/-! ### Vertices of a rung

PAPER (printed p. 50): *"every vertex of `A ∪ B ∪ C` belongs to a path between `A` and `B` with
only its first vertex in `A`, only its last vertex in `B`, and interior in `C`"*.  Read the
other way round, a rung's vertices are its two ends together with interior vertices, hence lie
in `A ∪ B ∪ C = V(S)`.  The paper uses this constantly and never states it. -/

/-- Every vertex of a path with named ends is one of the two ends or an interior vertex. -/
private theorem mem_ends_or_interior {G : SimpleGraph V} {C : Set V} {p : List V} {a b : V}
    (hp : IsPathFrom G p a b) (hint : ∀ v ∈ SPGT.interior p, v ∈ C)
    {u : V} (hu : u ∈ p) : u = a ∨ u = b ∨ u ∈ C := by
  by_cases h1 : u = a
  · exact Or.inl h1
  by_cases h2 : u = b
  · exact Or.inr (Or.inl h2)
  exact Or.inr (Or.inr (hint u ((mem_interior_iff_of_pathFrom hp).mpr ⟨hu, h1, h2⟩)))

/-- Repackaging of `IsSRung G (A, C, B) p`: the ends, and the trichotomy every vertex of the
rung satisfies. -/
theorem isSRung_trichotomy {G : SimpleGraph V} {A C B : Set V} {p : List V}
    (h : IsSRung G (A, C, B) p) :
    ∃ a b : V, IsPathFrom G p a b ∧ a ∈ A ∧ b ∈ B ∧
      (∀ u ∈ p, u = a ∨ u = b ∨ u ∈ C) := by
  obtain ⟨a, b, hpath, ha, hb, _, _, hint⟩ := h
  exact ⟨a, b, hpath, ha, hb, fun u hu => mem_ends_or_interior hpath hint hu⟩

/-- **Every vertex of an `S`-rung lies in `V(S)`.** -/
theorem mem_stripVertices_of_isSRung {G : SimpleGraph V} {S : Set V × Set V × Set V}
    {p : List V} (h : IsSRung G S p) {u : V} (hu : u ∈ p) : u ∈ stripVertices S := by
  obtain ⟨A, C, B⟩ := S
  obtain ⟨a, b, _, ha, hb, htri⟩ := isSRung_trichotomy h
  simp only [stripVertices, Set.mem_union]
  rcases htri u hu with rfl | rfl | h'
  · exact Or.inl (Or.inl ha)
  · exact Or.inl (Or.inr hb)
  · exact Or.inr h'

/-! ### Reversing a strip

PAPER (printed p. 50): *"The reverse of a strip `(A, C, B)` is the strip `(B, C, A)`."*  The
paper reverses strips freely (*"By reversing `S₂` we may assume …"*, *"By reversing each `Tⱼ`
if necessary …"*, *"Note that if we replace some `(Aᵢ, Cᵢ, Bᵢ)` by its reverse, we obtain
another striation"*); these lemmas are the formal content of those phrases. -/

@[simp] theorem reverseStrip_reverseStrip (S : Set V × Set V × Set V) :
    reverseStrip (reverseStrip S) = S := by
  obtain ⟨A, C, B⟩ := S; rfl

@[simp] theorem stripVertices_reverseStrip (S : Set V × Set V × Set V) :
    stripVertices (reverseStrip S) = stripVertices S := by
  obtain ⟨A, C, B⟩ := S
  simp only [reverseStrip, stripVertices]
  ext v
  simp only [Set.mem_union]
  tauto

/-- **Reversing a strip swaps the roles of the two end-sets**: the rungs of the reversed strip
are the reversed rungs. -/
theorem isSRung_reverse {G : SimpleGraph V} {S : Set V × Set V × Set V} {p : List V}
    (h : IsSRung G S p) : IsSRung G (reverseStrip S) p.reverse := by
  obtain ⟨A, C, B⟩ := S
  obtain ⟨a, b, hpath, ha, hb, htail, hdrop, hint⟩ := h
  have hnd : p.Nodup := path_nodup hpath.1
  have hne : p ≠ [] := path_ne_nil hpath.1
  have hndr : p.reverse.Nodup := by simpa using hnd
  have hner : p.reverse ≠ [] := by simpa using hne
  have hlast : p.getLast hne = b := by
    have := List.getLast?_eq_some_getLast (l := p) hne
    rw [hpath.2.2] at this
    exact (Option.some.injEq _ _ ▸ this).symm
  have hrhead : p.reverse.head? = some b := by rw [List.head?_reverse]; exact hpath.2.2
  have hrlast : p.reverse.getLast hner = a := by
    have h1 : p.reverse.getLast? = some a := by rw [List.getLast?_reverse]; exact hpath.2.1
    have := List.getLast?_eq_some_getLast (l := p.reverse) hner
    rw [h1] at this
    exact (Option.some.injEq _ _ ▸ this).symm
  refine ⟨b, a, isPathFrom_reverse hpath, hb, ha, ?_, ?_, ?_⟩
  · -- no later vertex of `p.reverse` lies in `B`
    intro v hv
    obtain ⟨hv1, hv2⟩ := (mem_tail_iff_of_nodup hndr hrhead).mp hv
    refine hdrop v ((mem_dropLast_iff hnd hne).mpr ⟨List.mem_reverse.mp hv1, ?_⟩)
    rw [hlast]; exact hv2
  · -- no earlier vertex of `p.reverse` lies in `A`
    intro v hv
    obtain ⟨hv1, hv2⟩ := (mem_dropLast_iff hndr hner).mp hv
    rw [hrlast] at hv2
    exact htail v ((mem_tail_iff_of_nodup hnd hpath.2.1).mpr ⟨List.mem_reverse.mp hv1, hv2⟩)
  · -- the interior is reversal-invariant
    intro v hv
    exact hint v (mem_interior_reverse.mp hv)

theorem isStrip_reverseStrip {G : SimpleGraph V} {S : Set V × Set V × Set V}
    (h : IsStrip G S) : IsStrip G (reverseStrip S) := by
  obtain ⟨A, C, B⟩ := S
  obtain ⟨hAB, hAC, hBC, hA, hB, hcov⟩ := h
  refine ⟨hAB.symm, hBC, hAC, hB, hA, ?_⟩
  intro v hv
  have hv' : v ∈ A ∪ B ∪ C := by
    simp only [Set.mem_union] at hv ⊢; tauto
  obtain ⟨p, hp, hvp⟩ := hcov v hv'
  exact ⟨p.reverse, by simpa [reverseStrip] using isSRung_reverse hp,
    List.mem_reverse.mpr hvp⟩

theorem isAntistrip_reverseStrip {G : SimpleGraph V} {T : Set V × Set V × Set V}
    (h : IsAntistrip G T) : IsAntistrip G (reverseStrip T) := isStrip_reverseStrip h

/-! ### Parallel and co-parallel under reversal

PAPER (printed p. 50): *"We say `S, T` are co-parallel if `S, T'` are parallel, where `T'` is
the reverse of `T`."*  Reversing either side of the pair therefore toggles parallel and
co-parallel. -/

/-- Reversing the **strip** toggles parallel and co-parallel. -/
theorem parallel_reverseStrip_left {G : SimpleGraph V} (S T : Set V × Set V × Set V) :
    ParallelStripAntistrip G (reverseStrip S) T ↔ CoParallel G S T := by
  obtain ⟨A, C, B⟩ := S
  obtain ⟨X, Z, Y⟩ := T
  simp only [reverseStrip, CoParallel, ParallelStripAntistrip]
  tauto

/-- Reversing the **antistrip** toggles parallel and co-parallel; this direction is the
definition of `CoParallel`. -/
theorem parallel_reverseStrip_right {G : SimpleGraph V} (S T : Set V × Set V × Set V) :
    ParallelStripAntistrip G S (reverseStrip T) ↔ CoParallel G S T := Iff.rfl

theorem coParallel_reverseStrip_right {G : SimpleGraph V} (S T : Set V × Set V × Set V) :
    CoParallel G S (reverseStrip T) ↔ ParallelStripAntistrip G S T := by
  rw [CoParallel, reverseStrip_reverseStrip]

theorem coParallel_reverseStrip_left {G : SimpleGraph V} (S T : Set V × Set V × Set V) :
    CoParallel G (reverseStrip S) T ↔ ParallelStripAntistrip G S T := by
  rw [CoParallel, parallel_reverseStrip_left, coParallel_reverseStrip_right]

/-! ### Reading off the edges and nonedges of a parallel pair

These two lemmas are each used four times in `isKnot_of_parallel_config` — three times in the
parallel orientation and once, with `X` and `Y` exchanged, in the co-parallel one.  That single
exchanged use is what makes the fourth clause of `IsKnot` the twisted one. -/

/-- PAPER (printed p. 47, third bullet of the definition of a knot): *"the only edges between
`V(Pᵢ)` and `{xⱼ, yⱼ}` are `aᵢxⱼ` and `bᵢyⱼ`"*.

For a rung `a-p-b` of `S = (A, C, B)` parallel to the antistrip `(X, Z, Y)` with `x ∈ X`,
`y ∈ Y`: `ax` is an edge because `A` is complete to `X ∪ Z`; `by` is an edge because `B` is
complete to `Y ∪ Z`; `ay` is a nonedge because `Y` is anticomplete to `A ∪ C`; `bx` is a
nonedge because `X` is anticomplete to `B ∪ C`; and an interior vertex of `p` lies in `C`,
which both `X` and `Y` are anticomplete to. -/
private theorem edges_of_parallel {G : SimpleGraph V} {A C B X Z Y : Set V}
    {p : List V} {a b x y : V}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (hXY : Disjoint X Y)
    (ha : a ∈ A) (hb : b ∈ B) (hx : x ∈ X) (hy : y ∈ Y)
    (htri : ∀ u ∈ p, u = a ∨ u = b ∨ u ∈ C)
    (cA : Complete G A (X ∪ Z)) (cB : Complete G B (Y ∪ Z))
    (aX : Anticomplete G X (B ∪ C)) (aY : Anticomplete G Y (A ∪ C))
    (u : V) (hu : u ∈ p) (w : V) (hw : w = x ∨ w = y) :
    (G.Adj u w ↔ ((u = a ∧ w = x) ∨ (u = b ∧ w = y))) := by
  have hab : a ≠ b := fun h => Set.disjoint_left.mp hAB ha (h ▸ hb)
  have hxy : x ≠ y := fun h => Set.disjoint_left.mp hXY hx (h ▸ hy)
  have hCa : ∀ {v : V}, v ∈ C → v ≠ a := fun hv h =>
    Set.disjoint_right.mp hAC hv (h ▸ ha)
  have hCb : ∀ {v : V}, v ∈ C → v ≠ b := fun hv h =>
    Set.disjoint_right.mp hBC hv (h ▸ hb)
  rcases hw with rfl | rfl
  · -- `w = x`
    rcases htri u hu with rfl | rfl | huC
    · exact ⟨fun _ => Or.inl ⟨rfl, rfl⟩, fun _ => cA u ha w (Set.mem_union_left Z hx)⟩
    · refine ⟨fun hadj => absurd hadj (fun h => aX w hx u (Set.mem_union_left C hb) h.symm), ?_⟩
      rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact absurd h.symm hab
      · exact absurd h hxy
    · refine ⟨fun hadj =>
        absurd hadj (fun h => aX w hx u (Set.mem_union_right B huC) h.symm), ?_⟩
      rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact absurd h (hCa huC)
      · exact absurd h (hCb huC)
  · -- `w = y`
    rcases htri u hu with rfl | rfl | huC
    · refine ⟨fun hadj => absurd hadj (fun h => aY w hy u (Set.mem_union_left C ha) h.symm), ?_⟩
      rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact absurd h.symm hxy
      · exact absurd h hab
    · exact ⟨fun _ => Or.inr ⟨rfl, rfl⟩, fun _ => cB u hb w (Set.mem_union_left Z hy)⟩
    · refine ⟨fun hadj =>
        absurd hadj (fun h => aY w hy u (Set.mem_union_right A huC) h.symm), ?_⟩
      rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact absurd h (hCa huC)
      · exact absurd h (hCb huC)

/-- PAPER (printed p. 47, fourth bullet of the definition of a knot): *"the only nonedges
between `V(Qⱼ)` and `{aᵢ, bᵢ}` are `aᵢyⱼ` and `bᵢxⱼ`"*.

For an antirung `x-q-y` of `(X, Z, Y)` and a strip `(A, C, B)` parallel to it: `a` is complete
to `X ∪ Z`, which contains `x` and the whole interior of `q`, and `a` is non-adjacent to `y`;
`b` is complete to `Y ∪ Z` and non-adjacent to `x`. -/
private theorem nonedges_of_parallel {G : SimpleGraph V} {A C B X Z Y : Set V}
    {q : List V} {a b x y : V}
    (hAB : Disjoint A B) (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (ha : a ∈ A) (hb : b ∈ B) (hx : x ∈ X) (hy : y ∈ Y)
    (htri : ∀ u ∈ q, u = x ∨ u = y ∨ u ∈ Z)
    (cA : Complete G A (X ∪ Z)) (cB : Complete G B (Y ∪ Z))
    (aX : Anticomplete G X (B ∪ C)) (aY : Anticomplete G Y (A ∪ C))
    (u : V) (hu : u ∈ q) (w : V) (hw : w = a ∨ w = b) :
    (¬ G.Adj u w ↔ ((w = a ∧ u = y) ∨ (w = b ∧ u = x))) := by
  have hab : a ≠ b := fun h => Set.disjoint_left.mp hAB ha (h ▸ hb)
  have hxy : x ≠ y := fun h => Set.disjoint_left.mp hXY hx (h ▸ hy)
  have hZx : ∀ {v : V}, v ∈ Z → v ≠ x := fun hv h =>
    Set.disjoint_right.mp hXZ hv (h ▸ hx)
  have hZy : ∀ {v : V}, v ∈ Z → v ≠ y := fun hv h =>
    Set.disjoint_right.mp hYZ hv (h ▸ hy)
  rcases hw with rfl | rfl
  · -- `w = a`
    rcases htri u hu with rfl | rfl | huZ
    · refine ⟨fun hn => absurd (cA w ha u (Set.mem_union_left Z hx)).symm hn, ?_⟩
      rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact absurd h hxy
      · exact absurd h hab
    · exact ⟨fun _ => Or.inl ⟨rfl, rfl⟩, fun _ => aY u hy w (Set.mem_union_left C ha)⟩
    · refine ⟨fun hn => absurd (cA w ha u (Set.mem_union_right X huZ)).symm hn, ?_⟩
      rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact absurd h (hZy huZ)
      · exact absurd h hab
  · -- `w = b`
    rcases htri u hu with rfl | rfl | huZ
    · exact ⟨fun _ => Or.inr ⟨rfl, rfl⟩, fun _ => aX u hx w (Set.mem_union_left C hb)⟩
    · refine ⟨fun hn => absurd (cB w hb u (Set.mem_union_left Z hy)).symm hn, ?_⟩
      rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact absurd h hab.symm
      · exact absurd h hxy.symm
    · refine ⟨fun hn => absurd (cB w hb u (Set.mem_union_right Y huZ)).symm hn, ?_⟩
      rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact absurd h hab.symm
      · exact absurd h (hZx huZ)

/-! ### The oriented case -/

/-- **The oriented case**: `S₁, S₂` both parallel to `T₁`, `S₁` parallel and `S₂` co-parallel
to `T₂`.  This is the configuration the paper normalises to by *"reversing `S₂`"*, and the four
rungs then form a knot.

PAPER (printed p. 51, inside the proof of 9.4): *"By reversing `S₂` we may assume that `S₁` and
`S₂` agree on `T₁`; and we may assume they disagree on `T₂`.  Let `a₂-P₂-b₂` be any `S₂`-rung,
and `x₂-Q₂-y₂` any `T₂`-antirung.  Then `(P₁, P₂, Q₁, Q₂)` is a knot."* -/
theorem isKnot_of_parallel_config {G : SimpleGraph V}
    {S₁ S₂ T₁ T₂ : Set V × Set V × Set V} {P₁ P₂ Q₁ Q₂ : List V}
    (hS₁ : IsStrip G S₁) (hS₂ : IsStrip G S₂)
    (hT₁ : IsAntistrip G T₁) (hT₂ : IsAntistrip G T₂)
    (hdisjS : Disjoint (stripVertices S₁) (stripVertices S₂))
    (hdisjT : Disjoint (stripVertices T₁) (stripVertices T₂))
    (hdisj11 : Disjoint (stripVertices S₁) (stripVertices T₁))
    (hdisj12 : Disjoint (stripVertices S₁) (stripVertices T₂))
    (hdisj21 : Disjoint (stripVertices S₂) (stripVertices T₁))
    (hdisj22 : Disjoint (stripVertices S₂) (stripVertices T₂))
    (hSanti : Anticomplete G (stripVertices S₁) (stripVertices S₂))
    (hTcomp : Complete G (stripVertices T₁) (stripVertices T₂))
    (h11 : ParallelStripAntistrip G S₁ T₁)
    (h12 : ParallelStripAntistrip G S₁ T₂)
    (h21 : ParallelStripAntistrip G S₂ T₁)
    (h22 : CoParallel G S₂ T₂)
    (hP₁ : IsSRung G S₁ P₁) (hP₂ : IsSRung G S₂ P₂)
    (hQ₁ : IsSRung Gᶜ T₁ Q₁) (hQ₂ : IsSRung Gᶜ T₂ Q₂)
    (hlP₁ : 1 ≤ pathLength P₁) (hlP₂ : 1 ≤ pathLength P₂)
    (hlQ₁ : 1 ≤ pathLength Q₁) (hlQ₂ : 1 ≤ pathLength Q₂) :
    IsKnot G P₁ P₂ Q₁ Q₂ := by
  -- the six pairwise-disjointness clauses of `IsKnot`, via `V(rung) ⊆ V(strip)`
  have memP₁ : ∀ u ∈ P₁, u ∈ stripVertices S₁ := fun u hu =>
    mem_stripVertices_of_isSRung hP₁ hu
  have memP₂ : ∀ u ∈ P₂, u ∈ stripVertices S₂ := fun u hu =>
    mem_stripVertices_of_isSRung hP₂ hu
  have memQ₁ : ∀ u ∈ Q₁, u ∈ stripVertices T₁ := fun u hu =>
    mem_stripVertices_of_isSRung hQ₁ hu
  have memQ₂ : ∀ u ∈ Q₂, u ∈ stripVertices T₂ := fun u hu =>
    mem_stripVertices_of_isSRung hQ₂ hu
  have dP₁P₂ : ∀ v ∈ P₁, v ∉ P₂ := fun v hv hv' =>
    Set.disjoint_left.mp hdisjS (memP₁ v hv) (memP₂ v hv')
  have dP₁Q₁ : ∀ v ∈ P₁, v ∉ Q₁ := fun v hv hv' =>
    Set.disjoint_left.mp hdisj11 (memP₁ v hv) (memQ₁ v hv')
  have dP₁Q₂ : ∀ v ∈ P₁, v ∉ Q₂ := fun v hv hv' =>
    Set.disjoint_left.mp hdisj12 (memP₁ v hv) (memQ₂ v hv')
  have dP₂Q₁ : ∀ v ∈ P₂, v ∉ Q₁ := fun v hv hv' =>
    Set.disjoint_left.mp hdisj21 (memP₂ v hv) (memQ₁ v hv')
  have dP₂Q₂ : ∀ v ∈ P₂, v ∉ Q₂ := fun v hv hv' =>
    Set.disjoint_left.mp hdisj22 (memP₂ v hv) (memQ₂ v hv')
  have dQ₁Q₂ : ∀ v ∈ Q₁, v ∉ Q₂ := fun v hv hv' =>
    Set.disjoint_left.mp hdisjT (memQ₁ v hv) (memQ₂ v hv')
  -- "there are no edges between `P₁` and `P₂`, and `Q₁` is complete to `Q₂`"
  have hanti : Anticomplete G {v : V | v ∈ P₁} {v : V | v ∈ P₂} := fun u hu w hw =>
    hSanti u (memP₁ u hu) w (memP₂ w hw)
  have hcomp : Complete G {v : V | v ∈ Q₁} {v : V | v ∈ Q₂} := fun u hu w hw =>
    hTcomp u (memQ₁ u hu) w (memQ₂ w hw)
  clear hdisjS hdisjT hdisj11 hdisj12 hdisj21 hdisj22 hSanti hTcomp
  clear memP₁ memP₂ memQ₁ memQ₂
  -- now unfold the four triples and read off the adjacency data
  obtain ⟨A₁, C₁, B₁⟩ := S₁
  obtain ⟨A₂, C₂, B₂⟩ := S₂
  obtain ⟨X₁, Z₁, Y₁⟩ := T₁
  obtain ⟨X₂, Z₂, Y₂⟩ := T₂
  obtain ⟨a₁, b₁, hpa₁, ha₁, hb₁, tri₁⟩ := isSRung_trichotomy hP₁
  obtain ⟨a₂, b₂, hpa₂, ha₂, hb₂, tri₂⟩ := isSRung_trichotomy hP₂
  obtain ⟨x₁, y₁, hqa₁, hx₁, hy₁, triq₁⟩ := isSRung_trichotomy hQ₁
  obtain ⟨x₂, y₂, hqa₂, hx₂, hy₂, triq₂⟩ := isSRung_trichotomy hQ₂
  obtain ⟨hAB₁, hAC₁, hBC₁, -, -, -⟩ := hS₁
  obtain ⟨hAB₂, hAC₂, hBC₂, -, -, -⟩ := hS₂
  obtain ⟨hXY₁, hXZ₁, hYZ₁, -, -, -⟩ := hT₁
  obtain ⟨hXY₂, hXZ₂, hYZ₂, -, -, -⟩ := hT₂
  obtain ⟨⟨cA₁, cB₁⟩, ⟨aX₁, aY₁⟩⟩ := h11
  obtain ⟨⟨cA₁', cB₁'⟩, ⟨aX₂', aY₂'⟩⟩ := h12
  obtain ⟨⟨cA₂, cB₂⟩, ⟨aX₁', aY₁'⟩⟩ := h21
  simp only [CoParallel, reverseStrip] at h22
  obtain ⟨⟨cA₂', cB₂'⟩, ⟨aY₂'', aX₂''⟩⟩ := h22
  -- `triq₂` with the two ends exchanged, for the co-parallel instantiation
  have triq₂' : ∀ u ∈ Q₂, u = y₂ ∨ u = x₂ ∨ u ∈ Z₂ := by
    intro u hu; rcases triq₂ u hu with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  refine ⟨a₁, b₁, a₂, b₂, x₁, y₁, x₂, y₂, hpa₁, hpa₂, hqa₁, hqa₂,
    dP₁P₂, dP₁Q₁, dP₁Q₂, dP₂Q₁, dP₂Q₂, dQ₁Q₂,
    hlP₁, hlP₂, hlQ₁, hlQ₂, hanti, hcomp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `(i,j) = (1,1)`: edges between `V(P₁)` and `{x₁, y₁}`
    intro u hu w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    exact edges_of_parallel hAB₁ hAC₁ hBC₁ hXY₁ ha₁ hb₁ hx₁ hy₁ tri₁ cA₁ cB₁ aX₁ aY₁ u hu w hw
  · -- `(i,j) = (1,2)`
    intro u hu w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    exact edges_of_parallel hAB₁ hAC₁ hBC₁ hXY₂ ha₁ hb₁ hx₂ hy₂ tri₁ cA₁' cB₁' aX₂' aY₂'
      u hu w hw
  · -- `(i,j) = (2,1)`
    intro u hu w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    exact edges_of_parallel hAB₂ hAC₂ hBC₂ hXY₁ ha₂ hb₂ hx₁ hy₁ tri₂ cA₂ cB₂ aX₁' aY₁'
      u hu w hw
  · -- `(i,j) = (2,2)`: the twisted clause, from `S₂` **co**-parallel to `T₂`
    intro u hu w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    exact edges_of_parallel hAB₂ hAC₂ hBC₂ hXY₂.symm ha₂ hb₂ hy₂ hx₂ tri₂ cA₂' cB₂'
      aY₂'' aX₂'' u hu w hw.symm
  · -- nonedges between `V(Q₁)` and `{a₁, b₁}`
    intro u hu w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    exact nonedges_of_parallel hAB₁ hXY₁ hXZ₁ hYZ₁ ha₁ hb₁ hx₁ hy₁ triq₁ cA₁ cB₁ aX₁ aY₁
      u hu w hw
  · -- nonedges between `V(Q₂)` and `{a₁, b₁}`
    intro u hu w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    exact nonedges_of_parallel hAB₁ hXY₂ hXZ₂ hYZ₂ ha₁ hb₁ hx₂ hy₂ triq₂ cA₁' cB₁'
      aX₂' aY₂' u hu w hw
  · -- nonedges between `V(Q₁)` and `{a₂, b₂}`
    intro u hu w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    exact nonedges_of_parallel hAB₂ hXY₁ hXZ₁ hYZ₁ ha₂ hb₂ hx₁ hy₁ triq₁ cA₂ cB₂
      aX₁' aY₁' u hu w hw
  · -- nonedges between `V(Q₂)` and `{a₂, b₂}`: again the co-parallel instantiation
    intro u hu w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    exact nonedges_of_parallel hAB₂ hXY₂.symm hYZ₂ hXZ₂ ha₂ hb₂ hy₂ hx₂ triq₂' cA₂' cB₂'
      aY₂'' aX₂'' u hu w hw

/-! ### The form a striation hands you -/

/-- **A twist inside a striation gives a knot** on any choice of rungs and antirungs, after
possibly reversing some of the four lists.

PAPER (printed p. 51, inside the proof of 9.4, and again in 9.5 and in claim (3) of 9.6):
*"By reversing `S₂` we may assume that `S₁` and `S₂` agree on `T₁`; and we may assume they
disagree on `T₂`.  Let `a₂-P₂-b₂` be any `S₂`-rung, and `x₂-Q₂-y₂` any `T₂`-antirung.  Then
`(P₁, P₂, Q₁, Q₂)` is a knot."*

The "reversing" is discharged here: the eight configurations a twist allows are normalised to
the pattern of `isKnot_of_parallel_config` by reversing at most `T₁`, `T₂` and `S₂` (never
`S₁`), as explained in the module header. -/
theorem exists_knot_of_twist {G : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (hL : IsStriation G S T) {i i' : Fin m} {j j' : Fin n}
    (hii : i ≠ i') (hjj : j ≠ j')
    (htw : IsTwist G (S i) (S i') (T j) (T j'))
    {P₁ P₂ Q₁ Q₂ : List V}
    (hP₁ : IsSRung G (S i) P₁) (hP₂ : IsSRung G (S i') P₂)
    (hQ₁ : IsSRung Gᶜ (T j) Q₁) (hQ₂ : IsSRung Gᶜ (T j') Q₂) :
    ∃ P₁' P₂' Q₁' Q₂' : List V,
      (P₁' = P₁ ∨ P₁' = P₁.reverse) ∧ (P₂' = P₂ ∨ P₂' = P₂.reverse) ∧
      (Q₁' = Q₁ ∨ Q₁' = Q₁.reverse) ∧ (Q₂' = Q₂ ∨ Q₂' = Q₂.reverse) ∧
      IsKnot G P₁' P₂' Q₁' Q₂' := by
  obtain ⟨hstrip, hantis, hdS, hdT, hdST, hoddS, hoddT, -, -, hantic, hcompl, -, -, -⟩ := hL
  -- "all their rungs and antirungs have odd length", so all four have length `≥ 1`
  have oddPos : ∀ {k : ℕ}, Odd k → 1 ≤ k := by rintro k ⟨t, rfl⟩; omega
  have hlP₁ : 1 ≤ pathLength P₁ := oddPos (hoddS i P₁ hP₁)
  have hlP₂ : 1 ≤ pathLength P₂ := oddPos (hoddS i' P₂ hP₂)
  have hlQ₁ : 1 ≤ pathLength Q₁ := oddPos (hoddT j Q₁ hQ₁)
  have hlQ₂ : 1 ≤ pathLength Q₂ := oddPos (hoddT j' Q₂ hQ₂)
  -- "all the strips and antistrips are pairwise disjoint"
  have hdisjS : Disjoint (stripVertices (S i)) (stripVertices (S i')) := hdS i i' hii
  have hdisjT : Disjoint (stripVertices (T j)) (stripVertices (T j')) := hdT j j' hjj
  have hdisj11 : Disjoint (stripVertices (S i)) (stripVertices (T j)) := hdST i j
  have hdisj12 : Disjoint (stripVertices (S i)) (stripVertices (T j')) := hdST i j'
  have hdisj21 : Disjoint (stripVertices (S i')) (stripVertices (T j)) := hdST i' j
  have hdisj22 : Disjoint (stripVertices (S i')) (stripVertices (T j')) := hdST i' j'
  -- "`Sᵢ` is anticomplete to `Sᵢ'`" / "`Tⱼ` is complete to `Tⱼ'`", recorded only for `i < i'`
  have hSanti : Anticomplete G (stripVertices (S i)) (stripVertices (S i')) := by
    rcases lt_trichotomy i i' with h | h | h
    · exact hantic i i' h
    · exact absurd h hii
    · exact anticomplete_symm (hantic i' i h)
  have hTcomp : Complete G (stripVertices (T j)) (stripVertices (T j')) := by
    rcases lt_trichotomy j j' with h | h | h
    · exact hcompl j j' h
    · exact absurd h hjj
    · exact complete_symm (hcompl j' j h)
  have hstripS₁ : IsStrip G (S i) := hstrip i
  have hstripS₂ : IsStrip G (S i') := hstrip i'
  have hantiT₁ : IsAntistrip G (T j) := hantis j
  have hantiT₂ : IsAntistrip G (T j') := hantis j'
  -- a single applier: `S i` and `P₁` are never reversed, the other three may be
  have app : ∀ (S₂' T₁' T₂' : Set V × Set V × Set V) (P₂' Q₁' Q₂' : List V),
      IsStrip G S₂' → IsAntistrip G T₁' → IsAntistrip G T₂' →
      stripVertices S₂' = stripVertices (S i') →
      stripVertices T₁' = stripVertices (T j) →
      stripVertices T₂' = stripVertices (T j') →
      IsSRung G S₂' P₂' → IsSRung Gᶜ T₁' Q₁' → IsSRung Gᶜ T₂' Q₂' →
      1 ≤ pathLength P₂' → 1 ≤ pathLength Q₁' → 1 ≤ pathLength Q₂' →
      ParallelStripAntistrip G (S i) T₁' → ParallelStripAntistrip G (S i) T₂' →
      ParallelStripAntistrip G S₂' T₁' → CoParallel G S₂' T₂' →
      IsKnot G P₁ P₂' Q₁' Q₂' := by
    intro S₂' T₁' T₂' P₂' Q₁' Q₂' hs2 ht1 ht2 e1 e2 e3 r1 r2 r3 l1 l2 l3 p11 p12 p21 p22
    refine isKnot_of_parallel_config hstripS₁ hs2 ht1 ht2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      p11 p12 p21 p22 hP₁ r1 r2 r3 hlP₁ l1 l2 l3
    · rw [e1]; exact hdisjS
    · rw [e2, e3]; exact hdisjT
    · rw [e2]; exact hdisj11
    · rw [e3]; exact hdisj12
    · rw [e1, e2]; exact hdisj21
    · rw [e1, e3]; exact hdisj22
    · rw [e1]; exact hSanti
    · rw [e2, e3]; exact hTcomp
  -- reversed data, prepared once
  have rs2 : IsStrip G (reverseStrip (S i')) := isStrip_reverseStrip hstripS₂
  have rt1 : IsAntistrip G (reverseStrip (T j)) := isAntistrip_reverseStrip hantiT₁
  have rt2 : IsAntistrip G (reverseStrip (T j')) := isAntistrip_reverseStrip hantiT₂
  have rrP₂ : IsSRung G (reverseStrip (S i')) P₂.reverse := isSRung_reverse hP₂
  have rrQ₁ : IsSRung Gᶜ (reverseStrip (T j)) Q₁.reverse := isSRung_reverse hQ₁
  have rrQ₂ : IsSRung Gᶜ (reverseStrip (T j')) Q₂.reverse := isSRung_reverse hQ₂
  have rlP₂ : 1 ≤ pathLength P₂.reverse := by rwa [pathLength_reverse]
  have rlQ₁ : 1 ≤ pathLength Q₁.reverse := by rwa [pathLength_reverse]
  have rlQ₂ : 1 ≤ pathLength Q₂.reverse := by rwa [pathLength_reverse]
  -- the eight configurations a twist allows
  rcases htw with ⟨hag, hdis⟩ | ⟨hag, hdis⟩
  · rcases hag with ⟨b11, b21⟩ | ⟨b11, b21⟩ <;> rcases hdis with ⟨b12, b22⟩ | ⟨b12, b22⟩
    · -- (∥, ∥, ∥, co) — already normalised
      exact ⟨P₁, P₂, Q₁, Q₂, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl,
        app (S i') (T j) (T j') P₂ Q₁ Q₂ hstripS₂ hantiT₁ hantiT₂ rfl rfl rfl
          hP₂ hQ₁ hQ₂ hlP₂ hlQ₁ hlQ₂ b11 b12 b21 b22⟩
    · -- (∥, co, ∥, ∥) — reverse `T₂`
      exact ⟨P₁, P₂, Q₁, Q₂.reverse, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inr rfl,
        app (S i') (T j) (reverseStrip (T j')) P₂ Q₁ Q₂.reverse hstripS₂ hantiT₁ rt2
          rfl rfl (stripVertices_reverseStrip _) hP₂ hQ₁ rrQ₂ hlP₂ hlQ₁ rlQ₂
          b11 ((parallel_reverseStrip_right _ _).mpr b12) b21
          ((coParallel_reverseStrip_right _ _).mpr b22)⟩
    · -- (co, ∥, co, co) — reverse `T₁`
      exact ⟨P₁, P₂, Q₁.reverse, Q₂, Or.inl rfl, Or.inl rfl, Or.inr rfl, Or.inl rfl,
        app (S i') (reverseStrip (T j)) (T j') P₂ Q₁.reverse Q₂ hstripS₂ rt1 hantiT₂
          rfl (stripVertices_reverseStrip _) rfl hP₂ rrQ₁ hQ₂ hlP₂ rlQ₁ hlQ₂
          ((parallel_reverseStrip_right _ _).mpr b11) b12
          ((parallel_reverseStrip_right _ _).mpr b21) b22⟩
    · -- (co, co, co, ∥) — reverse `T₁` and `T₂`
      exact ⟨P₁, P₂, Q₁.reverse, Q₂.reverse, Or.inl rfl, Or.inl rfl, Or.inr rfl, Or.inr rfl,
        app (S i') (reverseStrip (T j)) (reverseStrip (T j')) P₂ Q₁.reverse Q₂.reverse
          hstripS₂ rt1 rt2 rfl (stripVertices_reverseStrip _) (stripVertices_reverseStrip _)
          hP₂ rrQ₁ rrQ₂ hlP₂ rlQ₁ rlQ₂
          ((parallel_reverseStrip_right _ _).mpr b11)
          ((parallel_reverseStrip_right _ _).mpr b12)
          ((parallel_reverseStrip_right _ _).mpr b21)
          ((coParallel_reverseStrip_right _ _).mpr b22)⟩
  · rcases hag with ⟨b12, b22⟩ | ⟨b12, b22⟩ <;> rcases hdis with ⟨b11, b21⟩ | ⟨b11, b21⟩
    · -- (∥, ∥, co, ∥) — reverse `S₂`
      exact ⟨P₁, P₂.reverse, Q₁, Q₂, Or.inl rfl, Or.inr rfl, Or.inl rfl, Or.inl rfl,
        app (reverseStrip (S i')) (T j) (T j') P₂.reverse Q₁ Q₂ rs2 hantiT₁ hantiT₂
          (stripVertices_reverseStrip _) rfl rfl rrP₂ hQ₁ hQ₂ rlP₂ hlQ₁ hlQ₂
          b11 b12 ((parallel_reverseStrip_left _ _).mpr b21)
          ((coParallel_reverseStrip_left _ _).mpr b22)⟩
    · -- (co, ∥, ∥, ∥) — reverse `T₁` and `S₂`
      exact ⟨P₁, P₂.reverse, Q₁.reverse, Q₂, Or.inl rfl, Or.inr rfl, Or.inr rfl, Or.inl rfl,
        app (reverseStrip (S i')) (reverseStrip (T j)) (T j') P₂.reverse Q₁.reverse Q₂
          rs2 rt1 hantiT₂ (stripVertices_reverseStrip _) (stripVertices_reverseStrip _) rfl
          rrP₂ rrQ₁ hQ₂ rlP₂ rlQ₁ hlQ₂
          ((parallel_reverseStrip_right _ _).mpr b11) b12
          ((parallel_reverseStrip_left _ _).mpr ((coParallel_reverseStrip_right _ _).mpr b21))
          ((coParallel_reverseStrip_left _ _).mpr b22)⟩
    · -- (∥, co, co, co) — reverse `T₂` and `S₂`
      exact ⟨P₁, P₂.reverse, Q₁, Q₂.reverse, Or.inl rfl, Or.inr rfl, Or.inl rfl, Or.inr rfl,
        app (reverseStrip (S i')) (T j) (reverseStrip (T j')) P₂.reverse Q₁ Q₂.reverse
          rs2 hantiT₁ rt2 (stripVertices_reverseStrip _) rfl (stripVertices_reverseStrip _)
          rrP₂ hQ₁ rrQ₂ rlP₂ hlQ₁ rlQ₂
          b11 ((parallel_reverseStrip_right _ _).mpr b12)
          ((parallel_reverseStrip_left _ _).mpr b21)
          ((coParallel_reverseStrip_left _ _).mpr
            ((coParallel_reverseStrip_right _ _).mpr b22))⟩
    · -- (co, co, ∥, co) — reverse all three
      exact ⟨P₁, P₂.reverse, Q₁.reverse, Q₂.reverse, Or.inl rfl, Or.inr rfl, Or.inr rfl,
        Or.inr rfl,
        app (reverseStrip (S i')) (reverseStrip (T j)) (reverseStrip (T j'))
          P₂.reverse Q₁.reverse Q₂.reverse rs2 rt1 rt2
          (stripVertices_reverseStrip _) (stripVertices_reverseStrip _)
          (stripVertices_reverseStrip _) rrP₂ rrQ₁ rrQ₂ rlP₂ rlQ₁ rlQ₂
          ((parallel_reverseStrip_right _ _).mpr b11)
          ((parallel_reverseStrip_right _ _).mpr b12)
          ((parallel_reverseStrip_left _ _).mpr ((coParallel_reverseStrip_right _ _).mpr b21))
          ((coParallel_reverseStrip_left _ _).mpr
            ((coParallel_reverseStrip_right _ _).mpr b22))⟩

end Workspace.ProofLemmas.KnotFromTwist
