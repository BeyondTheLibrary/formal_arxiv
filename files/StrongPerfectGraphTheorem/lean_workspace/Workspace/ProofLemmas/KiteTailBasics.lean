import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.WheelSystemBasics
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.OptimalWheelChoice

/-!
# §22 — kites and tails: constructors, destructors, and the facts the printed proofs use silently

`Workspace.Types.WheelSystems` fixes the two pieces of §22 vocabulary:

* `IsKite G C Y y` — PAPER (printed p. 136): *"Let `(C,Y)` be a wheel in `G`.  A kite for
  `(C,Y)` is a vertex `y ∈ V(G) \ (Y ∪ V(C))`, not `Y`-complete, that has at least four
  neighbours in `C`, three of which are consecutive and `Y`-complete."*
* `IsTail G C Y z x₀ x₁ T` — PAPER (printed p. 136), the published three-bullet definition.

Both are flat nested conjunctions, so this module supplies named constructors (clauses in the
paper's own order) and named destructors, plus the small geometric facts that the printed
proofs of 22.1–22.5 use without comment.  Nothing here corresponds to a numbered result.

## What the printed proofs need

The opening sentence of **22.3** and of **22.5** is literally the same:

> *"Let `A₀ = V(C) \ {z, x₀, x₁}`, so `x₀, x₁` is a wheel system with respect to `(z, A₀)`,
> and `x₀, x₁` are `Y ∪ {y}`-complete."*

Unpacked, that one sentence asserts (a) `(z, A₀)` is a frame, (b) `x₀, x₁` is a wheel system of
height `1` for it, and (c) the hub is enlarged by `y`.  All three are proved here, as
`isFrame_rim_minus`, `isWheelSystem_rim_pair` and `vertexComplete_union_singleton` /
`anticonnectedSet_union_singleton`.  The geometric content behind (a) and (b) is:

* a hole has no triangle (`hole_no_triangle`) and, once its length is `≥ 5`, no four-cycle
  (`hole_no_four_cycle`);
* every rim vertex has exactly two neighbours on the rim (`exists_rimNeighbours`), which is
  the paper's *"let `x₀, x₁` be the neighbours of `z` in `C`"* — the phrase that opens 22.3,
  22.4, 22.5 and 23.2;
* deleting a vertex of the rim together with its two rim neighbours leaves a *connected* arc
  (`connectedSet_rim_minus`), which is the only nontrivial clause of `IsFrame`.

The relation *"`x₀, x₁` are the neighbours of `z` in `C`"* is spelled `IsRimNeighbours`, chosen
to be **definitionally the third clause of `IsTail`**, so `tail_rimNeighbours` is a projection.

## The bridge to `OptimalWheel`

`OptimalWheel G C Y` (the standing hypothesis of 23.1 and 22.3–22.5, with
`Workspace.ProofLemmas.OptimalWheelChoice.exists_optimal_wheel` supplying it) says the hub
cannot be enlarged.  Its one use in §22 is the last step of 22.3 and 22.5: *"there is no wheel
with hub `Y ∪ {y}`"*, which is `no_wheel_hub_union_singleton`.

## Encoding note on the kite's consecutive triple

*"three of which are consecutive"* is `∃ k : ℕ, [a, b, c] <+: C.rotate k`.  `hole_triple`
decodes such a prefix into membership, distinctness, the two rim edges `ba`, `bc`, the
non-edge `ac`, and — the clause the paper actually uses — *"`a` and `c` are **the** neighbours
of `b` in `C`"*.  That is what turns 22.3's *"let `x₀`-`z`-`x₁` be a subpath of `C`"* into a
frame.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.KiteTailBasics

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {C T t : List V} {Y : Set V} {y z x₀ x₁ p q : V}

/-! ## 0. Small list and cardinality helpers -/

private theorem exists_four_cons {l : List V} (h : 4 ≤ l.length) :
    ∃ (a b c : V) (r : List V), l = a :: b :: c :: r := by
  match l, h with
  | a :: b :: c :: r, _ => exact ⟨a, b, c, r, rfl⟩

/-- Three vertices span at most three vertices. -/
private theorem ncard_triple_le (a b c : V) : ({a, b, c} : Set V).ncard ≤ 3 := by
  have h1 : ({a, b, c} : Set V).ncard ≤ ({b, c} : Set V).ncard + 1 := Set.ncard_insert_le _ _
  have h2 : ({b, c} : Set V).ncard ≤ ({c} : Set V).ncard + 1 := Set.ncard_insert_le _ _
  have h3 : ({c} : Set V).ncard = 1 := Set.ncard_singleton _
  omega

/-- Four distinct vertices cannot all lie in a set of at most three vertices. -/
private theorem exists_of_four_notMem {a b c d : V} (S : Set V) (hS : S.ncard ≤ 3)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∃ v : V, (v = a ∨ v = b ∨ v = c ∨ v = d) ∧ v ∉ S := by
  by_contra hcon
  have hsub : ({a, b, c, d} : Set V) ⊆ S := by
    intro v hv
    by_contra hvS
    refine hcon ⟨v, ?_, hvS⟩
    simpa using hv
  have h4 : ({a, b, c, d} : Set V).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [hab, hac, had]),
      Set.ncard_insert_of_notMem (by simp [hbc, hbd]),
      Set.ncard_insert_of_notMem (by simp [hcd]), Set.ncard_singleton]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

/-- The vertex set of a list whose consecutive entries are adjacent is connected.  An *arc* of
the rim is the §22 instance; `connectedSet_of_isPathList` below is the general one. -/
theorem connectedSet_of_consecutive_adj : ∀ (l : List V),
    (∀ (i : ℕ) (hi : i + 1 < l.length), G.Adj (l[i]'(Nat.lt_of_succ_lt hi)) (l[i + 1]'hi)) →
      ConnectedSet G {v : V | v ∈ l} := by
  intro l
  induction l with
  | nil =>
    intro _
    have he : {v : V | v ∈ ([] : List V)} = (∅ : Set V) := by ext v; simp
    rw [he]
    intro a _
    exact absurd a.2 (Set.notMem_empty _)
  | cons a l ih =>
    intro h
    rcases l with _ | ⟨b, l'⟩
    · have he : {v : V | v ∈ [a]} = ({a} : Set V) := by ext v; simp
      rw [he]
      intro u v
      exact (Subtype.ext (u.2.trans v.2.symm) ▸ SimpleGraph.Reachable.refl u)
    · have hrest : ConnectedSet G {v : V | v ∈ b :: l'} := by
        refine ih (fun i hi => ?_)
        have hi' : i + 1 + 1 < (a :: b :: l').length := by
          simp only [List.length_cons] at hi ⊢; omega
        simpa using h (i + 1) hi'
      have hset : {v : V | v ∈ a :: b :: l'} = {v : V | v ∈ b :: l'} ∪ {a} := by
        ext v
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff, List.mem_cons]
        tauto
      rw [hset]
      refine ConnectedSetUnionAttach.connectedSet_union_singleton hrest ⟨b, by simp, ?_⟩
      have h0 : (0 : ℕ) + 1 < (a :: b :: l').length := by simp
      simpa using h 0 h0

/-- **The vertex set of a path is connected.**  Used whenever the paper feeds a path it has
just constructed back into a maximality argument about a connected set (22.1's *"from the
maximality of `A_t`"*). -/
theorem connectedSet_of_isPathList {p : List V} (hp : IsPathList G p) :
    ConnectedSet G {v : V | v ∈ p} :=
  connectedSet_of_consecutive_adj p (fun i hi => PathBasics.path_adj_succ hp hi)

/-! ## 1. Hole geometry: triangles and four-cycles -/

/-- **A hole contains no triangle.**  Used silently every time the paper says that the two
neighbours of a rim vertex are non-adjacent. -/
theorem hole_no_triangle (hC : IsHoleList G C) {a b c : V}
    (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h1 : G.Adj a b) (h2 : G.Adj b c) : ¬ G.Adj a c := by
  intro h3
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
  have hnd := HoleBasics.hole_nodup hC
  have h4 : 4 ≤ C.length := hC.1
  have d1 : i ≠ j := fun e => hab (hnd.getElem_inj_iff.mpr e)
  have d2 : i ≠ k := fun e => hac (hnd.getElem_inj_iff.mpr e)
  have d3 : j ≠ k := fun e => hbc (hnd.getElem_inj_iff.mpr e)
  have c1 := WheelParity.hole_adj_index hC hi hj h1
  have c2 := WheelParity.hole_adj_index hC hj hk h2
  have c3 := WheelParity.hole_adj_index hC hi hk h3
  omega

/-- **A hole of length `≥ 5` contains no four-cycle.**  This is what forbids a vertex of
`V(C) \ {z, x₀, x₁}` from being `{x₀, x₁}`-complete — condition 1 of a wheel system. -/
theorem hole_no_four_cycle (hC : IsHoleList G C) (hlen : 5 ≤ C.length) {a b c d : V}
    (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C) (hd : d ∈ C)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h1 : G.Adj a b) (h2 : G.Adj b c) (h3 : G.Adj c d) (h4 : G.Adj d a) : False := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hd
  have hnd := HoleBasics.hole_nodup hC
  have d1 : i ≠ j := fun e => hab (hnd.getElem_inj_iff.mpr e)
  have d2 : i ≠ k := fun e => hac (hnd.getElem_inj_iff.mpr e)
  have d3 : i ≠ l := fun e => had (hnd.getElem_inj_iff.mpr e)
  have d4 : j ≠ k := fun e => hbc (hnd.getElem_inj_iff.mpr e)
  have d5 : j ≠ l := fun e => hbd (hnd.getElem_inj_iff.mpr e)
  have d6 : k ≠ l := fun e => hcd (hnd.getElem_inj_iff.mpr e)
  have c1 := WheelParity.hole_adj_index hC hi hj h1
  have c2 := WheelParity.hole_adj_index hC hj hk h2
  have c3 := WheelParity.hole_adj_index hC hk hl h3
  have c4 := WheelParity.hole_adj_index hC hl hi h4
  omega

/-! ## 2. `IsRimNeighbours` — the paper's *"let `x₀, x₁` be the neighbours of `z` in `C`"* -/

/-- PAPER (printed p. 136, in the definition of a tail and in the statements of 22.3–22.5):
*"let `z ∈ V(C)`, and let `x₀, x₁` be the neighbours of `z` in `C`"*.

This is **definitionally** the third clause of
`Workspace.Types.WheelSystems.SPGT.IsTail`, so `tail_rimNeighbours` below is a projection. -/
def IsRimNeighbours (G : SimpleGraph V) (C : List V) (z x₀ x₁ : V) : Prop :=
  x₀ ≠ x₁ ∧ x₀ ∈ C ∧ x₁ ∈ C ∧ G.Adj z x₀ ∧ G.Adj z x₁ ∧
    ∀ w ∈ C, G.Adj z w → w = x₀ ∨ w = x₁

theorem isRimNeighbours_symm (h : IsRimNeighbours G C z x₀ x₁) :
    IsRimNeighbours G C z x₁ x₀ :=
  ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.2.1, h.2.2.2.1,
    fun w hw hadj => (h.2.2.2.2.2 w hw hadj).symm⟩

theorem isRimNeighbours_rotate {k : ℕ} :
    IsRimNeighbours G (C.rotate k) z x₀ x₁ ↔ IsRimNeighbours G C z x₀ x₁ := by
  simp only [IsRimNeighbours, List.mem_rotate]

/-- The two neighbours of a rim vertex are non-adjacent (a hole has no triangle). -/
theorem rimNeighbours_not_adj (hC : IsHoleList G C) (hz : z ∈ C)
    (h : IsRimNeighbours G C z x₀ x₁) : ¬ G.Adj x₀ x₁ :=
  hole_no_triangle hC h.2.1 hz h.2.2.1 h.2.2.2.1.ne' h.1 h.2.2.2.2.1.ne
    h.2.2.2.1.symm h.2.2.2.2.1

/-- Two descriptions of *the* neighbours of `z` in `C` agree as unordered pairs. -/
theorem rimNeighbours_pair_eq (h₁ : IsRimNeighbours G C z x₀ x₁)
    (h₂ : IsRimNeighbours G C z p q) : ({x₀, x₁} : Set V) = {p, q} := by
  ext v
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl)
    · exact h₂.2.2.2.2.2 v h₁.2.1 h₁.2.2.2.1
    · exact h₂.2.2.2.2.2 v h₁.2.2.1 h₁.2.2.2.2.1
  · rintro (rfl | rfl)
    · exact h₁.2.2.2.2.2 v h₂.2.1 h₂.2.2.2.1
    · exact h₁.2.2.2.2.2 v h₂.2.2.1 h₂.2.2.2.2.1

theorem rimNeighbours_triple_eq (h₁ : IsRimNeighbours G C z x₀ x₁)
    (h₂ : IsRimNeighbours G C z p q) : ({z, x₀, x₁} : Set V) = {z, p, q} :=
  congrArg (insert z) (rimNeighbours_pair_eq h₁ h₂)

/-! ## 3. Three cyclically consecutive vertices of a hole -/

/-- The hole obtained by rotating so that a prescribed triple heads the list. -/
theorem isHoleList_of_prefix_triple (hC : IsHoleList G C) {a b c : V} {r : List V} {k : ℕ}
    (hrot : C.rotate k = a :: b :: c :: r) : IsHoleList G (a :: b :: c :: r) := by
  have h := HoleBasics.isHoleList_rotate hC k
  rwa [hrot] at h

/-- **Decoder for a consecutive triple in normal position.**  For a hole listed as
`a :: b :: c :: r`, the vertices `a` and `c` are *the* neighbours of `b`. -/
theorem isRimNeighbours_head_triple {a b c : V} {r : List V}
    (hD : IsHoleList G (a :: b :: c :: r)) : IsRimNeighbours G (a :: b :: c :: r) b a c := by
  have hlen : 4 ≤ (a :: b :: c :: r).length := hD.1
  have h0 : (0 : ℕ) < (a :: b :: c :: r).length := by simp
  have h1 : (1 : ℕ) < (a :: b :: c :: r).length := by simp
  have h2 : (2 : ℕ) < (a :: b :: c :: r).length := by simp
  have hac : a ≠ c := by
    have := HoleBasics.hole_ne_of_ne_index hD h0 h2 (by omega)
    simpa using this
  have hba : G.Adj b a := by
    have := HoleBasics.hole_adj_succ hD (i := 0) (by simp)
    exact (by simpa using this : G.Adj a b).symm
  have hbc : G.Adj b c := by
    have := HoleBasics.hole_adj_succ hD (i := 1) (by simp only [List.length_cons]; omega)
    simpa using this
  refine ⟨hac, by simp, by simp, hba, hbc, ?_⟩
  intro w hw hadj
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hw
  have hb1 : (a :: b :: c :: r)[1]'h1 = b := by simp
  have hidx := WheelParity.hole_adj_index hD h1 hm (by rw [hb1]; exact hadj)
  have hm2 : m = 2 ∨ m = 0 := by omega
  rcases hm2 with rfl | rfl
  · right; simp
  · left; simp

/-- **Decoder for the kite's *"three consecutive"* clause.**  From
`∃ k, [a, b, c] <+: C.rotate k` read off: the three vertices lie on `C`, `a ≠ c`, the two rim
edges `ba`, `bc`, and that `a`, `c` are *the* neighbours of `b` in `C`.

This is what turns 22.3's *"let `x₀`-`z`-`x₁` be a subpath of `C`"* into a frame. -/
theorem hole_triple (hC : IsHoleList G C) {a b c : V}
    (hpre : ∃ k : ℕ, [a, b, c] <+: C.rotate k) :
    a ∈ C ∧ b ∈ C ∧ c ∈ C ∧ IsRimNeighbours G C b a c := by
  obtain ⟨k, r, hr⟩ := hpre
  have hrot : C.rotate k = a :: b :: c :: r := hr.symm
  have hD := isHoleList_of_prefix_triple hC hrot
  have hnb : IsRimNeighbours G C b a c := by
    have h := isRimNeighbours_head_triple hD
    rw [← hrot] at h
    exact isRimNeighbours_rotate.mp h
  have hb : b ∈ C := by
    have : b ∈ C.rotate k := by rw [hrot]; simp
    exact List.mem_rotate.mp this
  exact ⟨hnb.2.1, hb, hnb.2.2.1, hnb⟩

/-! ## 4. Normal form for a rim vertex, and the frame `A₀ = V(C) \ {z, x₀, x₁}` -/

/-- Rotate the rim so that `z` occupies position `1`; its two neighbours are then the entries
on either side of it. -/
theorem exists_rim_normal_form (hC : IsHoleList G C) (hz : z ∈ C) :
    ∃ (a c : V) (r : List V) (k : ℕ), C.rotate k = a :: z :: c :: r := by
  obtain ⟨i, hi, hzi⟩ := List.getElem_of_mem hz
  have h4 : 4 ≤ C.length := hC.1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = (i + (C.length - 1)) % C.length := ⟨_, rfl⟩
  have hrotlen : (C.rotate k).length = C.length := List.length_rotate C k
  obtain ⟨a, z', c, r, hDeq⟩ :=
    exists_four_cons (l := C.rotate k) (by omega)
  have hkey : (1 + k) % C.length = i := by
    rw [hk, Nat.add_mod_mod, show 1 + (i + (C.length - 1)) = i + C.length by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  have hlt1 : 1 < (C.rotate k).length := by omega
  have e2 : (C.rotate k)[1]'hlt1 = C[(1 + k) % C.length]'(Nat.mod_lt _ (by omega)) :=
    List.getElem_rotate C k 1 hlt1
  have e3 : C[(1 + k) % C.length]'(Nat.mod_lt _ (by omega)) = C[i]'hi :=
    (HoleBasics.hole_nodup hC).getElem_inj_iff.mpr hkey
  have e4 : (C.rotate k)[1]'hlt1 = z := by rw [e2, e3, hzi]
  -- `getElem?` carries no proof term, so rewriting the list under it is safe
  have e5 : (C.rotate k)[1]? = some z := by rw [List.getElem?_eq_getElem hlt1, e4]
  rw [hDeq] at e5
  have hz' : z' = z := by simpa using e5
  exact ⟨a, c, r, k, by rw [hDeq, hz']⟩

/-- The paper's `A₀ = V(C) \ {z, x₀, x₁}` in normal position is the vertex set of the arc `r`. -/
theorem rim_minus_eq_arc {a c : V} {r : List V} {k : ℕ}
    (hD : IsHoleList G (a :: z :: c :: r)) (hrot : C.rotate k = a :: z :: c :: r) :
    {v : V | v ∈ C} \ ({z, a, c} : Set V) = {v : V | v ∈ r} := by
  have hnd := hD.2.1
  have hat : a ∉ r := fun h =>
    (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
  have hzt : z ∉ r := fun h =>
    (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (List.mem_cons_of_mem _ h)
  have hct : c ∉ r := fun h =>
    (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).2).1 h
  have hmem : ∀ v : V, v ∈ C ↔ (v = a ∨ v = z ∨ v = c ∨ v ∈ r) := by
    intro v
    rw [← List.mem_rotate (l := C) (a := v) (n := k), hrot]
    simp only [List.mem_cons]
  ext v
  simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  rw [hmem v]
  constructor
  · rintro ⟨hv, hvz, hva, hvc⟩
    rcases hv with rfl | rfl | rfl | hv
    · exact absurd rfl hva
    · exact absurd rfl hvz
    · exact absurd rfl hvc
    · exact hv
  · intro hv
    refine ⟨Or.inr (Or.inr (Or.inr hv)), ?_, ?_, ?_⟩
    · rintro rfl; exact hzt hv
    · rintro rfl; exact hat hv
    · rintro rfl; exact hct hv

/-- The arc left over after deleting a rim vertex and its two rim neighbours is connected. -/
theorem connectedSet_arc {a c : V} {r : List V}
    (hD : IsHoleList G (a :: z :: c :: r)) : ConnectedSet G {v : V | v ∈ r} := by
  refine connectedSet_of_consecutive_adj r (fun i hi => ?_)
  have h1 : i + 3 + 1 < (a :: z :: c :: r).length := by
    simp only [List.length_cons]; omega
  exact HoleBasics.hole_adj_succ hD h1

/-- **PAPER (22.3, 22.5, printed pp. 138–139):** *"let `x₀, x₁` be the neighbours of `z` in
`C`"*.  Every vertex of a hole has exactly two neighbours on it. -/
theorem exists_rimNeighbours (hC : IsHoleList G C) (hz : z ∈ C) :
    ∃ a c : V, IsRimNeighbours G C z a c := by
  obtain ⟨a, c, r, k, hrot⟩ := exists_rim_normal_form hC hz
  have hD := isHoleList_of_prefix_triple hC hrot
  have h := isRimNeighbours_head_triple hD
  rw [← hrot] at h
  exact ⟨a, c, isRimNeighbours_rotate.mp h⟩

/-- Every rim vertex has a rim neighbour other than a prescribed one. -/
theorem exists_other_rim_nbr (hC : IsHoleList G C) {u : V} (hu : u ∈ C)
    (hz : z ∈ C) (hadj : G.Adj u z) : ∃ v ∈ C, G.Adj u v ∧ v ≠ z := by
  obtain ⟨a, c, hnb⟩ := exists_rimNeighbours hC hu
  rcases hnb.2.2.2.2.2 z hz hadj with rfl | rfl
  · exact ⟨c, hnb.2.2.1, hnb.2.2.2.2.1, Ne.symm hnb.1⟩
  · exact ⟨a, hnb.2.1, hnb.2.2.2.1, hnb.1⟩

/-- Membership test for the paper's `A₀`. -/
theorem mem_rim_minus {v : V} :
    v ∈ ({v : V | v ∈ C} \ ({z, x₀, x₁} : Set V)) ↔ (v ∈ C ∧ v ≠ z ∧ v ≠ x₀ ∧ v ≠ x₁) := by
  simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]

/-- `V(C) \ {z, x₀, x₁}` is connected. -/
theorem connectedSet_rim_minus (hC : IsHoleList G C) (hz : z ∈ C)
    (hnb : IsRimNeighbours G C z x₀ x₁) :
    ConnectedSet G ({v : V | v ∈ C} \ ({z, x₀, x₁} : Set V)) := by
  obtain ⟨a, c, r, k, hrot⟩ := exists_rim_normal_form hC hz
  have hD := isHoleList_of_prefix_triple hC hrot
  have hnb' : IsRimNeighbours G C z a c := by
    have h := isRimNeighbours_head_triple hD
    rw [← hrot] at h
    exact isRimNeighbours_rotate.mp h
  rw [rimNeighbours_triple_eq hnb hnb', rim_minus_eq_arc hD hrot]
  exact connectedSet_arc hD

/-- **PAPER (22.3, 22.5):** *"Let `A₀ = V(C) \ {z, x₀, x₁}`"* — this is a frame at `z`. -/
theorem isFrame_rim_minus (hC : IsHoleList G C) (hz : z ∈ C)
    (hnb : IsRimNeighbours G C z x₀ x₁) :
    IsFrame G z ({v : V | v ∈ C} \ ({z, x₀, x₁} : Set V)) := by
  obtain ⟨a, c, r, k, hrot⟩ := exists_rim_normal_form hC hz
  have hD := isHoleList_of_prefix_triple hC hrot
  have hnb' : IsRimNeighbours G C z a c := by
    have h := isRimNeighbours_head_triple hD
    rw [← hrot] at h
    exact isRimNeighbours_rotate.mp h
  have hconn := connectedSet_rim_minus hC hz hnb
  refine ⟨?_, hconn, ?_, ?_⟩
  · -- nonempty: the arc is non-null because the hole has at least four vertices
    rw [rimNeighbours_triple_eq hnb hnb', rim_minus_eq_arc hD hrot]
    have hlen : 4 ≤ (a :: z :: c :: r).length := hD.1
    have hne : r ≠ [] := by
      rintro rfl
      simp only [List.length_cons, List.length_nil] at hlen
      omega
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil r hne
    exact ⟨v, hv⟩
  · intro hzm
    exact (mem_rim_minus.mp hzm).2.1 rfl
  · intro v hvm hadj
    obtain ⟨hvC, hvz, hv0, hv1⟩ := mem_rim_minus.mp hvm
    rcases hnb.2.2.2.2.2 v hvC hadj with rfl | rfl
    · exact hv0 rfl
    · exact hv1 rfl

/-! ## 5. `x₀, x₁` is a wheel system of height 1 for the frame `(z, A₀)` -/

/-- No vertex of `A₀ = V(C) \ {z, x₀, x₁}` is `{x₀, x₁}`-complete — condition 1 of a wheel
system, and the hypothesis of `WheelSystemBasics.A₀_subset_wheelSystemA` at index `1`. -/
theorem no_pair_complete_rim_minus (hC : IsHoleList G C) (hlen : 5 ≤ C.length) (hz : z ∈ C)
    (hnb : IsRimNeighbours G C z x₀ x₁) :
    ∀ v ∈ ({v : V | v ∈ C} \ ({z, x₀, x₁} : Set V)), ¬ VertexComplete G v ({x₀, x₁} : Set V) := by
  intro v hvm hvc
  obtain ⟨hvC, hvz, hv0, hv1⟩ := mem_rim_minus.mp hvm
  have ha0 : G.Adj v x₀ := hvc x₀ (Set.mem_insert _ _)
  have ha1 : G.Adj v x₁ := hvc x₁ (Set.mem_insert_of_mem _ rfl)
  exact hole_no_four_cycle hC hlen hz hnb.2.1 hvC hnb.2.2.1
    hnb.2.2.2.1.ne (Ne.symm hvz) hnb.2.2.2.2.1.ne (Ne.symm hv0) hnb.1 hv1
    hnb.2.2.2.1 ha0.symm ha1 hnb.2.2.2.2.1.symm

/-- **PAPER (22.3, 22.5):** *"so `x₀, x₁` is a wheel system with respect to `(z, A₀)`"*.

Stated for an arbitrary `x : ℕ → V` (only `x 0` and `x 1` are constrained by a wheel system of
height `1`), so it plugs straight into the signatures of 22.1, 22.2 and 22.4. -/
theorem isWheelSystem_rim_pair (hC : IsHoleList G C) (hlen : 5 ≤ C.length) (hz : z ∈ C)
    (x : ℕ → V) (hnb : IsRimNeighbours G C z (x 0) (x 1)) :
    IsWheelSystem G z ({v : V | v ∈ C} \ ({z, x 0, x 1} : Set V)) x 1 := by
  have hnadj : ¬ G.Adj (x 0) (x 1) := rimNeighbours_not_adj hC hz hnb
  have hnbr : ∀ u : V, u ∈ C → G.Adj u z → u ≠ x 0 → u ≠ x 1 →
      True := fun _ _ _ _ _ => trivial
  -- a neighbour of `x 0` (resp. `x 1`) inside `A₀`
  have hother : ∀ u v : V, u ∈ C → G.Adj z u → IsRimNeighbours G C z u v →
      ∃ w ∈ ({v : V | v ∈ C} \ ({z, x 0, x 1} : Set V)), G.Adj u w := by
    intro u v huC hzu _
    obtain ⟨w, hwC, hadj, hwz⟩ := exists_other_rim_nbr hC huC hz hzu.symm
    refine ⟨w, mem_rim_minus.mpr ⟨hwC, hwz, ?_, ?_⟩, hadj⟩
    · rintro rfl
      rcases hnb.2.2.2.2.2 u huC hzu with rfl | rfl
      · exact G.irrefl hadj
      · exact hnadj hadj.symm
    · rintro rfl
      rcases hnb.2.2.2.2.2 u huC hzu with rfl | rfl
      · exact hnadj hadj
      · exact G.irrefl hadj
  refine ⟨le_refl 1, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- distinctness of `x 0`, `x 1`
    intro j hj k hk he
    interval_cases j <;> interval_cases k <;>
      first
        | rfl
        | exact absurd he hnb.1
        | exact absurd he.symm hnb.1
  · -- `x j ∉ A₀` and `x j ≠ z`
    intro j hj
    interval_cases j
    · exact ⟨fun hm => (mem_rim_minus.mp hm).2.2.1 rfl, hnb.2.2.2.1.ne'⟩
    · exact ⟨fun hm => (mem_rim_minus.mp hm).2.2.2 rfl, hnb.2.2.2.2.1.ne'⟩
  · exact hother (x 0) (x 1) hnb.2.1 hnb.2.2.2.1 hnb
  · exact hother (x 1) (x 0) hnb.2.2.1 hnb.2.2.2.2.1 (isRimNeighbours_symm hnb)
  · intro v hvm hvc
    exact no_pair_complete_rim_minus hC hlen hz hnb v hvm hvc
  · -- condition 2 is vacuous at height 1
    intro i h2 h1
    exact absurd h2 (by omega)
  · -- `x 1` is not `{x 0}`-complete
    intro i h1 h2
    obtain rfl : i = 1 := by omega
    intro hvc
    exact hnadj (hvc (x 0) (by
      rw [WheelSystemBasics.wheelSystemX_zero]; exact rfl)).symm
  · intro j hj
    interval_cases j
    · exact hnb.2.2.2.1
    · exact hnb.2.2.2.2.1

/-! ## 6. Enlarging the hub: `Y ∪ {y}` -/

/-- A `Y`-complete vertex adjacent to `y` is `Y ∪ {y}`-complete. -/
theorem vertexComplete_union_singleton {v : V} (hY : VertexComplete G v Y) (hadj : G.Adj v y) :
    VertexComplete G v (Y ∪ {y}) := by
  intro w hw
  rcases hw with hw | hw
  · exact hY w hw
  · exact (Set.mem_singleton_iff.mp hw) ▸ hadj

/-- **PAPER (22.3, 22.5), used silently:** enlarging an anticonnected hub by a vertex that is
*not* `Y`-complete keeps it anticonnected — the new vertex has a non-neighbour in `Y`, i.e. a
`Ḡ`-neighbour. -/
theorem anticonnectedSet_union_singleton (hY : AnticonnectedSet G Y)
    (hyc : ¬ VertexComplete G y Y) : AnticonnectedSet G (Y ∪ {y}) := by
  by_cases hyY : y ∈ Y
  · have he : Y ∪ ({y} : Set V) = Y :=
      Set.union_eq_self_of_subset_right (Set.singleton_subset_iff.mpr hyY)
    rw [he]
    exact hY
  · have hex : ∃ w ∈ Y, ¬ G.Adj y w := by
      by_contra hcon
      exact hyc (by
        intro w hw
        by_contra hnw
        exact hcon ⟨w, hw, hnw⟩)
    obtain ⟨w, hwY, hnw⟩ := hex
    have hne : y ≠ w := by rintro rfl; exact hyY hwY
    exact ConnectedSetUnionAttach.connectedSet_union_singleton (G := Gᶜ) hY
      ⟨w, hwY, ⟨hne, hnw⟩⟩

/-- `Y` is a proper subset of `Y ∪ {y}` when `y ∉ Y`. -/
theorem ssubset_union_singleton (hy : y ∉ Y) : Y ⊂ Y ∪ ({y} : Set V) :=
  (Set.ssubset_iff_of_subset Set.subset_union_left).mpr ⟨y, Or.inr rfl, hy⟩

/-! ## 7. `OptimalWheel` -/

theorem optimalWheel_isWheel (h : OptimalWheel G C Y) : IsWheel G C Y := h.1

/-- **PAPER (22.3, last sentence):** *"there is no wheel with hub `Y ∪ {y}`"*.  This is the one
place §22 uses the optimality of `(C, Y)`. -/
theorem no_wheel_hub_union_singleton (h : OptimalWheel G C Y) (hy : y ∉ Y) :
    ¬ ∃ C' : List V, IsWheel G C' (Y ∪ ({y} : Set V)) := by
  rintro ⟨C', hw'⟩
  exact h.2 ⟨C', Y ∪ {y}, hw', ssubset_union_singleton hy⟩

/-! ## 8. `IsWheel` projections used throughout §22 -/

theorem wheel_isHoleList (hw : IsWheel G C Y) : IsHoleList G C := hw.1.1

theorem wheel_six_le_length (hw : IsWheel G C Y) : 6 ≤ C.length := hw.1.2

theorem wheel_hub_nonempty (hw : IsWheel G C Y) : Y.Nonempty := hw.2.1.1

theorem wheel_hub_anticonnected (hw : IsWheel G C Y) : AnticonnectedSet G Y := hw.2.1.2.1

theorem wheel_rim_notMem_hub (hw : IsWheel G C Y) : ∀ v ∈ C, v ∉ Y := hw.2.1.2.2

/-- **Every member of the hub has a neighbour on the rim avoiding any three prescribed
vertices.**  This is the paper's *"thus every member of `Y ∪ {y}` has a neighbour in `A₀`"*
(22.3) and *"from the construction, all members of `Y` have a neighbour in `A₀`"* (22.5): the
two disjoint `Y`-complete edges of the rim supply four distinct vertices adjacent to every
member of `Y`, and at most three of them can be hit by `{z, x₀, x₁}`. -/
theorem exists_hub_nbr_outside (hw : IsWheel G C Y) {w : V} (hwY : w ∈ Y) (u₁ u₂ u₃ : V) :
    ∃ v ∈ C, G.Adj w v ∧ v ≠ u₁ ∧ v ≠ u₂ ∧ v ≠ u₃ := by
  obtain ⟨a, b, c, d, haC, hbC, hcC, hdC, hab, hcd, hac, had, hbc, hbd⟩ := hw.2.2
  obtain ⟨v, hv, hvS⟩ :=
    exists_of_four_notMem (a := a) (b := b) (c := c) (d := d) ({u₁, u₂, u₃} : Set V)
      (ncard_triple_le _ _ _) hab.1.ne hac had hbc hbd hcd.1.ne
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hvS
  refine ⟨v, ?_, ?_, hvS.1, hvS.2.1, hvS.2.2⟩
  · rcases hv with rfl | rfl | rfl | rfl
    · exact haC
    · exact hbC
    · exact hcC
    · exact hdC
  · rcases hv with rfl | rfl | rfl | rfl
    · exact (hab.2.1 w hwY).symm
    · exact (hab.2.2 w hwY).symm
    · exact (hcd.2.1 w hwY).symm
    · exact (hcd.2.2 w hwY).symm

/-- The same fact phrased against the paper's `A₀`: *"all members of `Y` have a neighbour in
`A₀`"* (22.5), *"every member of `Y ∪ {y}` has a neighbour in `A₀`"* (22.3, the `Y` half). -/
theorem hub_exists_nbr_rim_minus (hw : IsWheel G C Y) {w : V} (hwY : w ∈ Y) :
    ∃ a ∈ ({v : V | v ∈ C} \ ({z, x₀, x₁} : Set V)), G.Adj w a := by
  obtain ⟨v, hvC, hadj, h1, h2, h3⟩ := exists_hub_nbr_outside hw hwY z x₀ x₁
  exact ⟨v, mem_rim_minus.mpr ⟨hvC, h1, h2, h3⟩, hadj⟩

/-! ## 9. Kites: constructor, destructors, and the facts 22.3 uses -/

/-- **Constructor for `IsKite`, clauses in the paper's order.**

PAPER (printed p. 136): *"Let `(C,Y)` be a wheel in `G`.  A kite for `(C,Y)` is a vertex
`y ∈ V(G) \ (Y ∪ V(C))`, not `Y`-complete, that has at least four neighbours in `C`, three of
which are consecutive and `Y`-complete."* -/
theorem isKite_mk (hw : IsWheel G C Y) (hyY : y ∉ Y) (hyC : y ∉ C)
    (hync : ¬ VertexComplete G y Y)
    (hfour : 4 ≤ {v : V | v ∈ C ∧ G.Adj y v}.ncard)
    {a b c : V} (hcons : ∃ k : ℕ, [a, b, c] <+: C.rotate k)
    (hya : G.Adj y a) (hyb : G.Adj y b) (hyc : G.Adj y c)
    (haY : VertexComplete G a Y) (hbY : VertexComplete G b Y) (hcY : VertexComplete G c Y) :
    IsKite G C Y y :=
  ⟨hw, hyY, hyC, hync, hfour, a, b, c, hcons, hya, hyb, hyc, haY, hbY, hcY⟩

/-- **Constructor from a fourth neighbour**, which is how the count *"at least four neighbours
in `C`"* is actually verified (22.4, claims (2) and (7)): exhibit the consecutive triple plus
one further neighbour of `y` on the rim. -/
theorem isKite_of_triple_and_fourth (hw : IsWheel G C Y) (hyY : y ∉ Y) (hyC : y ∉ C)
    (hync : ¬ VertexComplete G y Y)
    {a b c d : V} (hcons : ∃ k : ℕ, [a, b, c] <+: C.rotate k)
    (hya : G.Adj y a) (hyb : G.Adj y b) (hyc : G.Adj y c)
    (haY : VertexComplete G a Y) (hbY : VertexComplete G b Y) (hcY : VertexComplete G c Y)
    (hdC : d ∈ C) (hyd : G.Adj y d) (hda : d ≠ a) (hdb : d ≠ b) (hdc : d ≠ c) :
    IsKite G C Y y := by
  obtain ⟨haC, hbC, hcC, hnb⟩ := hole_triple (wheel_isHoleList hw) hcons
  have hab : a ≠ b := hnb.2.2.2.1.ne'
  have hbc : b ≠ c := hnb.2.2.2.2.1.ne
  have hac : a ≠ c := hnb.1
  refine isKite_mk hw hyY hyC hync ?_ hcons hya hyb hyc haY hbY hcY
  have hsub : ({a, b, c, d} : Set V) ⊆ {v : V | v ∈ C ∧ G.Adj y v} := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact ⟨haC, hya⟩
    · exact ⟨hbC, hyb⟩
    · exact ⟨hcC, hyc⟩
    · exact ⟨hdC, hyd⟩
  have h4 : ({a, b, c, d} : Set V).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [hab, hac, Ne.symm hda]),
      Set.ncard_insert_of_notMem (by simp [hbc, Ne.symm hdb]),
      Set.ncard_insert_of_notMem (by simp [Ne.symm hdc]), Set.ncard_singleton]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

theorem kite_isWheel (h : IsKite G C Y y) : IsWheel G C Y := h.1

theorem kite_notMem_hub (h : IsKite G C Y y) : y ∉ Y := h.2.1

theorem kite_notMem_rim (h : IsKite G C Y y) : y ∉ C := h.2.2.1

theorem kite_not_vertexComplete (h : IsKite G C Y y) : ¬ VertexComplete G y Y := h.2.2.2.1

theorem kite_four_le_ncard (h : IsKite G C Y y) :
    4 ≤ {v : V | v ∈ C ∧ G.Adj y v}.ncard := h.2.2.2.2.1

theorem kite_exists_triple (h : IsKite G C Y y) :
    ∃ a b c : V, (∃ k : ℕ, [a, b, c] <+: C.rotate k) ∧
      G.Adj y a ∧ G.Adj y b ∧ G.Adj y c ∧
      VertexComplete G a Y ∧ VertexComplete G b Y ∧ VertexComplete G c Y := h.2.2.2.2.2

/-- **PAPER (22.3, first line of the proof):** *"Let `x₀`-`z`-`x₁` be a subpath of `C`, all
`Y`-complete and adjacent to `y`."*  The middle vertex `z` of the kite's consecutive triple is
a rim vertex whose two rim neighbours are the outer two. -/
theorem kite_spec (h : IsKite G C Y y) :
    ∃ x₀ w x₁ : V, w ∈ C ∧ IsRimNeighbours G C w x₀ x₁ ∧
      VertexComplete G x₀ Y ∧ VertexComplete G w Y ∧ VertexComplete G x₁ Y ∧
      G.Adj y x₀ ∧ G.Adj y w ∧ G.Adj y x₁ := by
  obtain ⟨a, b, c, hcons, hya, hyb, hyc, haY, hbY, hcY⟩ := kite_exists_triple h
  obtain ⟨haC, hbC, hcC, hnb⟩ := hole_triple (wheel_isHoleList (kite_isWheel h)) hcons
  exact ⟨a, b, c, hbC, hnb, haY, hbY, hcY, hya, hyb, hyc⟩

/-- **PAPER (22.3):** *"Thus every member of `Y ∪ {y}` has a neighbour in `A₀`"* — the `y` half.
A kite has four neighbours on the rim, so one of them avoids `{z, x₀, x₁}`. -/
theorem kite_exists_nbr_outside (h : IsKite G C Y y) (u₁ u₂ u₃ : V) :
    ∃ v ∈ C, G.Adj y v ∧ v ≠ u₁ ∧ v ≠ u₂ ∧ v ≠ u₃ := by
  by_contra hcon
  have hsub : {v : V | v ∈ C ∧ G.Adj y v} ⊆ ({u₁, u₂, u₃} : Set V) := by
    intro v hv
    by_contra hvS
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hvS
    exact hcon ⟨v, hv.1, hv.2, hvS.1, hvS.2.1, hvS.2.2⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h3 := ncard_triple_le u₁ u₂ u₃
  have h4 := kite_four_le_ncard h
  omega

/-! ## 10. Tails: constructor, destructors, and the facts 22.4/22.5 use -/

/-- **Constructor for `IsTail`, clauses in the paper's order.**

PAPER (printed p. 136): *"Let `(C,Y)` be a wheel in `G`, let `z ∈ V(C)`, and let `x₀, x₁` be
the neighbours of `z` in `C`.  A path `T` of `G \ {x₀,x₁}` from `z` to `V(C) \ {z,x₀,x₁}` is
called a tail for `z` (with respect to the wheel `(C,Y)`) if*

* *`x₀, z, x₁` are all `Y`-complete, and there is a `Y`-complete edge in `C \ {x₀,z,x₁}`*
* *the neighbour of `z` in `T` is adjacent to `x₀, x₁`, and*
* *no internal vertex of `T` is in `Y` or is `Y`-complete."* -/
theorem isTail_mk (hw : IsWheel G C Y) (hz : z ∈ C)
    (hnb : IsRimNeighbours G C z x₀ x₁)
    (havoid : ∀ v ∈ T, v ≠ x₀ ∧ v ≠ x₁)
    (hend : ∃ w : V, IsPathFrom G T z w ∧ w ∈ C ∧ w ≠ z ∧ w ≠ x₀ ∧ w ≠ x₁)
    (hc0 : VertexComplete G x₀ Y) (hcz : VertexComplete G z Y)
    (hc1 : VertexComplete G x₁ Y)
    (hedge : ∃ u v : V, u ∈ C ∧ v ∈ C ∧
      (u ≠ x₀ ∧ u ≠ z ∧ u ≠ x₁) ∧ (v ≠ x₀ ∧ v ≠ z ∧ v ≠ x₁) ∧ EdgeComplete G Y u v)
    (hshape : ∃ (u : V) (R : List V), T = z :: u :: R ∧ G.Adj u x₀ ∧ G.Adj u x₁)
    (hint : ∀ v ∈ SPGT.interior T, v ∉ Y ∧ ¬ VertexComplete G v Y) :
    IsTail G C Y z x₀ x₁ T :=
  ⟨hw, hz, hnb, havoid, hend, ⟨⟨hc0, hcz, hc1⟩, hedge⟩, hshape, hint⟩

theorem tail_isWheel (h : IsTail G C Y z x₀ x₁ T) : IsWheel G C Y := h.1

theorem tail_mem_rim (h : IsTail G C Y z x₀ x₁ T) : z ∈ C := h.2.1

/-- The preamble *"`x₀, x₁` are the neighbours of `z` in `C`"* is a projection, because
`IsRimNeighbours` was defined to be exactly that clause. -/
theorem tail_rimNeighbours (h : IsTail G C Y z x₀ x₁ T) : IsRimNeighbours G C z x₀ x₁ := h.2.2.1

/-- *"a path `T` of `G \ {x₀, x₁}`"*. -/
theorem tail_avoids (h : IsTail G C Y z x₀ x₁ T) : ∀ v ∈ T, v ≠ x₀ ∧ v ≠ x₁ := h.2.2.2.1

/-- *"from `z` to `V(C) \ {z, x₀, x₁}`"*. -/
theorem tail_exists_end (h : IsTail G C Y z x₀ x₁ T) :
    ∃ w : V, IsPathFrom G T z w ∧ w ∈ C ∧ w ≠ z ∧ w ≠ x₀ ∧ w ≠ x₁ := h.2.2.2.2.1

/-- First bullet, first half: *"`x₀, z, x₁` are all `Y`-complete"*. -/
theorem tail_complete_triple (h : IsTail G C Y z x₀ x₁ T) :
    VertexComplete G x₀ Y ∧ VertexComplete G z Y ∧ VertexComplete G x₁ Y := h.2.2.2.2.2.1.1

/-- First bullet, second half: *"there is a `Y`-complete edge in `C \ {x₀, z, x₁}`"*.
This is the clause claim (7) of 22.4 uses at the very end. -/
theorem tail_exists_yEdge (h : IsTail G C Y z x₀ x₁ T) :
    ∃ u v : V, u ∈ C ∧ v ∈ C ∧
      (u ≠ x₀ ∧ u ≠ z ∧ u ≠ x₁) ∧ (v ≠ x₀ ∧ v ≠ z ∧ v ≠ x₁) ∧
      EdgeComplete G Y u v := h.2.2.2.2.2.1.2

/-- Second bullet: *"the neighbour of `z` in `T` is adjacent to `x₀, x₁`"*. -/
theorem tail_shape (h : IsTail G C Y z x₀ x₁ T) :
    ∃ (u : V) (R : List V), T = z :: u :: R ∧ G.Adj u x₀ ∧ G.Adj u x₁ := h.2.2.2.2.2.2.1

/-- Third bullet: *"no internal vertex of `T` is in `Y` or is `Y`-complete"*. -/
theorem tail_interior (h : IsTail G C Y z x₀ x₁ T) :
    ∀ v ∈ SPGT.interior T, v ∉ Y ∧ ¬ VertexComplete G v Y := h.2.2.2.2.2.2.2

theorem tail_isPathList (h : IsTail G C Y z x₀ x₁ T) : IsPathList G T :=
  (tail_exists_end h).choose_spec.1.1

/-- **The neighbour `y` of `z` in `T`, with everything 22.4 and 22.5 assume about it.**

22.4 and 22.5 both put `y` into the hub (*"with hub `Y ∪ {y}`"*), which silently requires
`y ∉ Y` and `¬ VertexComplete G y Y`.  Neither is a clause of the published definition — the
published version only forbids *internal* vertices of `T` from lying in `Y`.  It nevertheless
follows, because `y` **is** internal: the last vertex of `T` lies on `C` while `y` does not
(`y` is adjacent to `z`, so if `y` were on `C` it would be `x₀` or `x₁`, which `T` avoids). -/
theorem tail_snd_spec (h : IsTail G C Y z x₀ x₁ T) :
    ∃ (u : V) (R : List V), T = z :: u :: R ∧ R ≠ [] ∧
      G.Adj z u ∧ G.Adj u x₀ ∧ G.Adj u x₁ ∧
      u ∉ C ∧ u ≠ z ∧ u ≠ x₀ ∧ u ≠ x₁ ∧
      u ∈ SPGT.interior T ∧ u ∉ Y ∧ ¬ VertexComplete G u Y := by
  obtain ⟨u, R, hTeq, hux₀, hux₁⟩ := tail_shape h
  obtain ⟨w, hpath, hwC, hwz, hwx₀, hwx₁⟩ := tail_exists_end h
  have hnb := tail_rimNeighbours h
  have havoid := tail_avoids h
  have hint := tail_interior h
  subst hTeq
  have hmemu : u ∈ (z :: u :: R) := by simp
  obtain ⟨hu0, hu1⟩ := havoid u hmemu
  have hzu : G.Adj z u := by
    have h0 : (0 : ℕ) + 1 < (z :: u :: R).length := by simp
    have hadj := PathBasics.path_adj_succ hpath.1 h0
    simpa using hadj
  have huC : u ∉ C := by
    intro huC
    rcases hnb.2.2.2.2.2 u huC hzu with he | he
    · exact hu0 he
    · exact hu1 he
  have huz : u ≠ z := by
    have hnd : (z :: u :: R).Nodup := hpath.1.2.1
    exact Ne.symm (List.ne_of_not_mem_cons (List.nodup_cons.mp hnd).1)
  have hRne : R ≠ [] := by
    rintro rfl
    have hlast : ([z, u] : List V).getLast? = some w := hpath.2.2
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hlast
    exact huC (hlast ▸ hwC)
  have huw : u ≠ w := by
    rintro rfl
    exact huC hwC
  have huint : u ∈ SPGT.interior (z :: u :: R) :=
    (PathBasics.mem_interior_iff_of_pathFrom hpath).mpr ⟨hmemu, huz, huw⟩
  obtain ⟨huY, hunc⟩ := hint u huint
  exact ⟨u, R, rfl, hRne, hzu, hux₀, hux₁, huC, huz, hu0, hu1, huint, huY, hunc⟩

/-- `z`, `x₀`, `x₁` all lie on the rim and hence outside the hub. -/
theorem tail_rim_notMem_hub (h : IsTail G C Y z x₀ x₁ T) :
    z ∉ Y ∧ x₀ ∉ Y ∧ x₁ ∉ Y :=
  ⟨wheel_rim_notMem_hub (tail_isWheel h) z (tail_mem_rim h),
    wheel_rim_notMem_hub (tail_isWheel h) x₀ (tail_rimNeighbours h).2.1,
    wheel_rim_notMem_hub (tail_isWheel h) x₁ (tail_rimNeighbours h).2.2.1⟩

/-- **PAPER (22.4):** *"since `T` is a tail it follows that none of `u₁, …, uₙ` are
`Y`-complete"* — the `uᵢ` are the vertices of `T` other than `z` and the far end. -/
theorem tail_notYComplete_of_mem (h : IsTail G C Y z x₀ x₁ T) {w : V}
    (hend : IsPathFrom G T z w) {v : V} (hv : v ∈ T) (hvz : v ≠ z) (hvw : v ≠ w) :
    v ∉ Y ∧ ¬ VertexComplete G v Y :=
  tail_interior h v ((PathBasics.mem_interior_iff_of_pathFrom hend).mpr ⟨hv, hvz, hvw⟩)

/-- **Composition with `Workspace.ProofLemmas.OptimalWheelChoice`.**  The first bullet of the
definition of a tail supplies a `Y`-complete edge of the rim, so the quantity
`OptimalWheelChoice.yEdgeCount` — the one minimised by `exists_optimal_wheel`, and the measure
step (1) of 23.2 decreases — is at least `1` as soon as some rim vertex has a tail. -/
theorem one_le_yEdgeCount_of_tail (h : IsTail G C Y z x₀ x₁ T) :
    1 ≤ OptimalWheelChoice.yEdgeCount G Y C := by
  obtain ⟨u, v, huC, hvC, -, -, hedge⟩ := tail_exists_yEdge h
  have hne : {e : Sym2 V | ∃ a ∈ C, ∃ b ∈ C, e = s(a, b) ∧ EdgeComplete G Y a b}.Nonempty :=
    ⟨s(u, v), u, huC, v, hvC, rfl, hedge⟩
  rw [OptimalWheelChoice.yEdgeCount_def]
  have hpos := (Set.ncard_pos (Set.toFinite _)).mpr hne
  omega

/-! ## 11. The composite opening move of 22.3 and 22.5

*"Let `A₀ = V(C) \ {z, x₀, x₁}`, so `x₀, x₁` is a wheel system with respect to `(z, A₀)`, and
`x₀, x₁` are `Y ∪ {y}`-complete."* -/

/-- The full opening move, packaged.  `y` is the kite (22.3) or the neighbour of `z` in the
tail (22.5); the hypotheses are exactly what both proofs have available at that point. -/
theorem opening_move (hw : IsWheel G C Y) (hz : z ∈ C) (x : ℕ → V)
    (hnb : IsRimNeighbours G C z (x 0) (x 1))
    (h0Y : VertexComplete G (x 0) Y) (h1Y : VertexComplete G (x 1) Y)
    (hy0 : G.Adj y (x 0)) (hy1 : G.Adj y (x 1)) :
    IsFrame G z ({v : V | v ∈ C} \ ({z, x 0, x 1} : Set V)) ∧
      IsWheelSystem G z ({v : V | v ∈ C} \ ({z, x 0, x 1} : Set V)) x 1 ∧
      VertexComplete G (x 0) (Y ∪ {y}) ∧ VertexComplete G (x 1) (Y ∪ {y}) := by
  have hC := wheel_isHoleList hw
  have hlen : 5 ≤ C.length := by have := wheel_six_le_length hw; omega
  exact ⟨isFrame_rim_minus hC hz hnb, isWheelSystem_rim_pair hC hlen hz x hnb,
    vertexComplete_union_singleton h0Y hy0.symm, vertexComplete_union_singleton h1Y hy1.symm⟩

/-- `A₀ ⊆ A₁`: the frame's own set is a member of the family defining `A₁`, because no vertex of
`A₀` is `X₁ = {x₀, x₁}`-complete.  This is what turns *"has a neighbour in `A₀`"* into 22.2's
hypothesis *"has a neighbour in `A_s`"* at `s = 1`. -/
theorem rim_minus_subset_wheelSystemA (hC : IsHoleList G C) (hlen : 5 ≤ C.length) (hz : z ∈ C)
    (x : ℕ → V) (hnb : IsRimNeighbours G C z (x 0) (x 1)) :
    ({v : V | v ∈ C} \ ({z, x 0, x 1} : Set V)) ⊆
      wheelSystemA G z ({v : V | v ∈ C} \ ({z, x 0, x 1} : Set V)) x 1 := by
  refine WheelSystemBasics.A₀_subset_wheelSystemA (isFrame_rim_minus hC hz hnb) ?_
  intro v hv hvc
  refine no_pair_complete_rim_minus hC hlen hz hnb v hv ?_
  intro u hu
  refine hvc u ?_
  rw [WheelSystemBasics.wheelSystemX_one]
  exact hu

/-- **PAPER (22.5, first two sentences):** *"Suppose `z ∈ V(C)` has a tail `T`; let `y` be the
neighbour of `z` in `T`, and let `x₀, x₁` be the neighbours of `z` in `C`.  Let
`A₀ = V(C) \ {z, x₀, x₁}`, so `x₀, x₁` is a wheel system with respect to `(z, A₀)`, and
`x₀, x₁` are `Y ∪ {y}`-complete.  ...  From the construction, all members of `Y` have a
neighbour in `A₀`."*

Everything 22.5 hands to 22.1, in one lemma.  `x : ℕ → V` is an arbitrary sequence whose first
two terms are the two rim neighbours of `z`; `u` is the paper's `y`, the neighbour of `z`
in `T`.  Note the last clause is stated for `Y` only, not for `Y ∪ {u}` — `u` need not have a
neighbour on the rim outside `{z, x₀, x₁}`, and 22.1 does not ask for one. -/
theorem tail_opening_move (h : IsTail G C Y z x₀ x₁ T) (x : ℕ → V)
    (hx0 : x 0 = x₀) (hx1 : x 1 = x₁) :
    ∃ u : V, (∃ R : List V, T = z :: u :: R) ∧
      u ∉ C ∧ u ∉ Y ∧ ¬ VertexComplete G u Y ∧
      IsFrame G z ({v : V | v ∈ C} \ ({z, x 0, x 1} : Set V)) ∧
      IsWheelSystem G z ({v : V | v ∈ C} \ ({z, x 0, x 1} : Set V)) x 1 ∧
      (Y ∪ ({u} : Set V)).Nonempty ∧
      AnticonnectedSet G (Y ∪ ({u} : Set V)) ∧
      VertexComplete G z (Y ∪ ({u} : Set V)) ∧
      (∀ i ≤ 1, VertexComplete G (x i) (Y ∪ ({u} : Set V))) ∧
      (∀ w ∈ Y ∪ ({u} : Set V),
        w ∉ ({v : V | v ∈ C} \ ({z, x 0, x 1} : Set V)) ∧ w ≠ z ∧ ∀ i ≤ 1, w ≠ x i) ∧
      (∀ w ∈ Y, ∃ a ∈ ({v : V | v ∈ C} \ ({z, x 0, x 1} : Set V)), G.Adj w a) := by
  have hw := tail_isWheel h
  have hC := wheel_isHoleList hw
  have hlen5 : 5 ≤ C.length := by have := wheel_six_le_length hw; omega
  have hz := tail_mem_rim h
  have hnb := tail_rimNeighbours h
  have hnb' : IsRimNeighbours G C z (x 0) (x 1) := by rw [hx0, hx1]; exact hnb
  obtain ⟨hc0, hcz, hc1⟩ := tail_complete_triple h
  obtain ⟨u, R, hTeq, -, hzu, hu0, hu1, huC, huz, hux0, hux1, -, huY, hunc⟩ :=
    tail_snd_spec h
  have hnotC : ∀ w : V, w ∈ Y ∪ ({u} : Set V) → w ∉ C := by
    rintro w (hwY | hwy)
    · exact fun hwC => wheel_rim_notMem_hub hw w hwC hwY
    · rw [Set.mem_singleton_iff] at hwy
      subst hwy
      exact huC
  refine ⟨u, ⟨R, hTeq⟩, huC, huY, hunc,
    isFrame_rim_minus hC hz hnb', isWheelSystem_rim_pair hC hlen5 hz x hnb',
    ⟨u, Or.inr rfl⟩,
    anticonnectedSet_union_singleton (wheel_hub_anticonnected hw) hunc,
    vertexComplete_union_singleton hcz hzu, ?_, ?_, ?_⟩
  · intro i hi
    interval_cases i
    · rw [hx0]; exact vertexComplete_union_singleton hc0 hu0.symm
    · rw [hx1]; exact vertexComplete_union_singleton hc1 hu1.symm
  · intro w hwm
    have hwC := hnotC w hwm
    refine ⟨fun hm => hwC (mem_rim_minus.mp hm).1, ?_, ?_⟩
    · rintro rfl; exact hwC hz
    · intro i hi
      interval_cases i
      · rw [hx0]; rintro rfl; exact hwC hnb.2.1
      · rw [hx1]; rintro rfl; exact hwC hnb.2.2.1
  · intro w hwY
    obtain ⟨a, ham, hadj⟩ := hub_exists_nbr_rim_minus (z := z) (x₀ := x 0) (x₁ := x 1) hw hwY
    exact ⟨a, ham, hadj⟩

/-! ## 12. Wheel-system surgery: truncating and re-indexing

22.1 returns an *extension* `x'` of the given sequence (`x' i = x i` for `i ≤ s`), and 19.1
quantifies over the *truncations* `fun j => if j ≤ r then x j else x (t+1)`.  Both moves need
that `Xᵢ` — and hence `Aᵢ` — only depends on the first `i + 1` terms.  The paper says this
once, parenthetically (*"it agrees with the `A_r` of the truncated system, since the two
systems have the same `X_r`"*), and then uses it silently in 22.2 and 22.5. -/

theorem wheelSystemX_congr {x x' : ℕ → V} {i : ℕ} (h : ∀ j ≤ i, x j = x' j) :
    wheelSystemX x i = wheelSystemX x' i := by
  ext v
  simp only [WheelSystemBasics.mem_wheelSystemX]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, h j hj⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, (h j hj).symm⟩

theorem wheelSystemA_congr {x x' : ℕ → V} {i : ℕ} {w : V} {A₀ : Set V}
    (h : ∀ j ≤ i, x j = x' j) :
    wheelSystemA G w A₀ x i = wheelSystemA G w A₀ x' i := by
  simp only [wheelSystemA, wheelSystemX_congr h]

/-- **The last vertex of a wheel system does not lie in its hub.**

Not a clause of any definition, and used silently by 22.2 (*"a vertex
`v ∉ Y ∪ {z, x₀,…,x_s}`"*, with `v = x_{t+1}`).  The argument: if `x_{t+1} ∈ Y` then each of
`x₀, …, x_t` is `Y`-complete and hence adjacent to `x_{t+1}`, making `x_{t+1}` itself
`X_t`-complete — which condition 3 of a wheel system forbids. -/
theorem hub_last_notMem {w : V} {A₀ : Set V} {x : ℕ → V} {n : ℕ} {Y : Set V}
    (hhub : IsHubForWheelSystem G w A₀ x (n + 1) Y) : x (n + 1) ∉ Y := by
  intro hmem
  refine hhub.1.2.2.2.2.2.1 (n + 1) (by omega) (le_refl _) ?_
  intro c hc
  obtain ⟨j, hj, rfl⟩ := WheelSystemBasics.mem_wheelSystemX.mp hc
  exact ((hhub.2.2.2.2.2.1 j (by omega)) (x (n + 1)) hmem).symm

/-- The vertices of a wheel system are pairwise distinct, so the last one differs from every
earlier one. -/
theorem hub_last_ne {w : V} {A₀ : Set V} {x : ℕ → V} {n i : ℕ} {Y : Set V}
    (hhub : IsHubForWheelSystem G w A₀ x (n + 1) Y) (hi : i ≤ n) : x (n + 1) ≠ x i := by
  intro he
  have := hhub.1.2.1 (n + 1) (le_refl _) i (by omega) he
  omega

/-- **No vertex of `A₀` is `X_t`-complete, for a wheel system of height `t`.**  For `t = 1`
this is condition 1 of the definition; for `t ≥ 2` it follows from condition 2 at `i = t`,
whose witness `B ⊇ A₀` has no `X_{t-1}`-complete vertex, together with the fact that being
`X_t`-complete is stronger than being `X_{t-1}`-complete. -/
theorem no_wheelSystemX_complete_A₀ {w : V} {A₀ : Set V} {x : ℕ → V} {n : ℕ}
    (hws : IsWheelSystem G w A₀ x n) :
    ∀ v ∈ A₀, ¬ VertexComplete G v (wheelSystemX x n) := by
  intro v hv hvc
  rcases eq_or_lt_of_le hws.1 with hn | hn
  · -- `n = 1`: condition 1
    have hn1 : n = 1 := hn.symm
    subst hn1
    refine hws.2.2.2.1.2.2 v hv ?_
    rw [← WheelSystemBasics.wheelSystemX_one x]
    exact hvc
  · -- `n ≥ 2`: condition 2 at `i = n`
    obtain ⟨B, hA₀B, -, -, -, hBX⟩ := hws.2.2.2.2.1 n (by omega) (le_refl n)
    exact hBX v (hA₀B hv)
      (WheelSystemBasics.vertexComplete_wheelSystemX_mono (by omega) hvc)

/-- **`A₀ ⊆ A_t`** for a wheel system of height `t` — so in particular `A_t` is nonempty.  The
paper writes *"So for each `i`, `A_{i−1} ⊆ Aᵢ`"* and then uses `A₀ ⊆ A_t` freely. -/
theorem A₀_subset_wheelSystemA_of_wheelSystem {w : V} {A₀ : Set V} {x : ℕ → V} {n : ℕ}
    (hframe : IsFrame G w A₀) (hws : IsWheelSystem G w A₀ x n) :
    A₀ ⊆ wheelSystemA G w A₀ x n :=
  WheelSystemBasics.A₀_subset_wheelSystemA hframe (no_wheelSystemX_complete_A₀ hws)

/-- A hub is disjoint from every `Aᵢ`: members of the hub are neighbours of `w`, and `Aᵢ`
contains none. -/
theorem hub_disjoint_wheelSystemA {w : V} {A₀ : Set V} {x : ℕ → V} {n i : ℕ} {Y : Set V}
    (hhub : IsHubForWheelSystem G w A₀ x (n + 1) Y) {c : V} (hc : c ∈ Y) :
    c ∉ wheelSystemA G w A₀ x i := fun hmem =>
  WheelSystemBasics.wheelSystemA_no_nbr hmem (hhub.2.2.2.2.1 c hc)

end Workspace.ProofLemmas.KiteTailBasics
