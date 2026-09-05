import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathGlue

/-!
# Hyperprisms — the vocabulary layer for §10 (*The even prism*)

The proof of **10.6** (printed pp. 60–63, the longest printed proof in the paper) is run
entirely inside a *hyperprism*: the collection of nine sets

```
A₁ C₁ B₁
A₂ C₂ B₂
A₃ C₃ B₃
```

introduced at the top of that proof and formalised as
`Workspace.Types.Prisms.SPGT.IsHyperprism`.  Every step of the printed argument reduces to
the same handful of moves, and this module supplies them once:

* **projections of `IsHyperprism`** — `complete_A`, `complete_B`, `cross` (the *"there are
  no other edges"* clause, usable for `i ≠ j` rather than only for `i < j`) and `notMem_S`
  (`Sᵢ ∩ Sⱼ = ∅`);
* **rungs with named ends** — `IsRungFrom G A B C i p x y` is `IsRungOfHyperprism` with its
  two existentials named, which is how the paper always uses it (*"choose an `i`-rung `Rᵢ`
  with ends `aᵢ ∈ Aᵢ` and `bᵢ ∈ Bᵢ`"*).  `rung_mem_S`, `rung_eq_A`, `rung_eq_B`,
  `rung_ends_ne`, `rung_two_le_length` are the basic facts;
* **two rungs of different indices close into a hole** — `rung_cross` (the exact adjacency
  pattern between them) and `rung_pair_hole` (`P ++ Q.reverse` is a hole).  This is the
  engine behind claim (1) and behind every *"… is an odd hole, a contradiction"* of the
  printed proof;
* **three rungs form a prism** — `rungs_formPrism`, the move that lets 10.3/10.5 be cited
  inside 10.6, and that produces the even prism in the last line of the proof;
* **claim (1)** of the printed proof — `rung_even`: *"For `1 ≤ i ≤ 3`, all `i`-rungs have
  even length."*
* `hyperVerts A B C` is the paper's `V(H)`, the union of the nine sets; it is the quantity
  the printed proof maximises.
-/

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.HyperprismBasics

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT

variable {V : Type*} {G : SimpleGraph V} {A B C : Fin 3 → Set V}

/-! ### Small utilities -/

theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide

private theorem dl {X Y : Set V} (h : Disjoint X Y) {x : V} (hx : x ∈ X) : x ∉ Y :=
  Set.disjoint_left.mp h hx

/-- A path whose two ends are distinct has at least two vertices. -/
theorem two_le_length_of_ends_ne {p : List V} {x y : V} (hp : IsPathFrom G p x y)
    (hxy : x ≠ y) : 2 ≤ p.length := by
  have hpos : 0 < p.length := PathBasics.path_length_pos hp.1
  rcases (show p.length = 1 ∨ 2 ≤ p.length by omega) with h1 | h2
  · exfalso
    obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h1
    have hx : c = x := by simpa using hp.2.1
    have hy : c = y := by simpa using hp.2.2
    exact hxy (hx.symm.trans hy)
  · exact h2

/-! ### `V(H)` -/

/-- The paper's `V(H)`: the union of the nine sets of the hyperprism.  This is the quantity
the proof of 10.6 chooses maximal. -/
def hyperVerts (A B C : Fin 3 → Set V) : Set V :=
  (A 0 ∪ B 0 ∪ C 0) ∪ (A 1 ∪ B 1 ∪ C 1) ∪ (A 2 ∪ B 2 ∪ C 2)

theorem mem_hyperVerts_iff {x : V} :
    x ∈ hyperVerts A B C ↔ ∃ i : Fin 3, x ∈ A i ∪ B i ∪ C i := by
  constructor
  · rintro ((h | h) | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  · rintro ⟨i, hi⟩
    rcases fin3_cases i with rfl | rfl | rfl
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi

theorem subset_hyperVerts (i : Fin 3) : A i ∪ B i ∪ C i ⊆ hyperVerts A B C :=
  fun _ hx => mem_hyperVerts_iff.mpr ⟨i, hx⟩

/-! ### Projections of `IsHyperprism` -/

theorem complete_A (hH : IsHyperprism G A B C) {i j : Fin 3} (hij : i ≠ j) :
    SPGT.Complete G (A i) (A j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact (hH.2.2.2.2.2.2.2.1 i j h).1
  · intro x hx y hy
    exact ((hH.2.2.2.2.2.2.2.1 j i h).1 y hy x hx).symm

theorem complete_B (hH : IsHyperprism G A B C) {i j : Fin 3} (hij : i ≠ j) :
    SPGT.Complete G (B i) (B j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact (hH.2.2.2.2.2.2.2.1 i j h).2.1
  · intro x hx y hy
    exact ((hH.2.2.2.2.2.2.2.1 j i h).2.1 y hy x hx).symm

/-- The *"there are no other edges between `Sᵢ` and `Sⱼ`"* clause, for arbitrary `i ≠ j`
(the definition states it only for `i < j`). -/
theorem cross (hH : IsHyperprism G A B C) {i j : Fin 3} (hij : i ≠ j) {u v : V}
    (hu : u ∈ A i ∪ B i ∪ C i) (hv : v ∈ A j ∪ B j ∪ C j) (hadj : G.Adj u v) :
    (u ∈ A i ∧ v ∈ A j) ∨ (u ∈ B i ∧ v ∈ B j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact (hH.2.2.2.2.2.2.2.1 i j h).2.2 u hu v hv hadj
  · rcases (hH.2.2.2.2.2.2.2.1 j i h).2.2 v hv u hu hadj.symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨h2, h1⟩

/-- `Sᵢ` and `Sⱼ` are disjoint for `i ≠ j`. -/
theorem notMem_S (hH : IsHyperprism G A B C) {i j : Fin 3} (hij : i ≠ j) {u : V}
    (hu : u ∈ A i ∪ B i ∪ C i) : u ∉ A j ∪ B j ∪ C j := by
  intro hj
  rcases hu with (hi | hi) | hi <;> rcases hj with (hj | hj) | hj
  · exact dl (hH.2.2.2.2.1 i j hij) hi hj
  · exact dl (hH.2.1 i j) hi hj
  · exact dl (hH.2.2.1 i j) hi hj
  · exact dl (hH.2.1 j i) hj hi
  · exact dl (hH.2.2.2.2.2.1 i j hij) hi hj
  · exact dl (hH.2.2.2.1 i j) hi hj
  · exact dl (hH.2.2.1 j i) hj hi
  · exact dl (hH.2.2.2.1 j i) hj hi
  · exact dl (hH.2.2.2.2.2.2.1 i j hij) hi hj

/-! ### Rungs with named ends -/

/-- `IsRungOfHyperprism` with its two existential ends named, which is how the paper always
uses it: *"choose an `i`-rung `Rᵢ` with ends `aᵢ ∈ Aᵢ` and `bᵢ ∈ Bᵢ`"*. -/
def IsRungFrom (G : SimpleGraph V) (A B C : Fin 3 → Set V) (i : Fin 3) (p : List V)
    (x y : V) : Prop :=
  x ∈ A i ∧ y ∈ B i ∧ IsPathFrom G p x y ∧ ∀ w ∈ SPGT.interior p, w ∈ C i

theorem isRungOfHyperprism_iff {i : Fin 3} {p : List V} :
    IsRungOfHyperprism G A B C i p ↔ ∃ x y, IsRungFrom G A B C i p x y := Iff.rfl

theorem isRungOfHyperprism_of_isRungFrom {i : Fin 3} {p : List V} {x y : V}
    (h : IsRungFrom G A B C i p x y) : IsRungOfHyperprism G A B C i p := ⟨x, y, h⟩

theorem rung_ends_ne (hH : IsHyperprism G A B C) {i : Fin 3} {p : List V} {x y : V}
    (hp : IsRungFrom G A B C i p x y) : x ≠ y := by
  intro h
  exact dl (hH.2.1 i i) hp.1 (by rw [h]; exact hp.2.1)

theorem rung_two_le_length (hH : IsHyperprism G A B C) {i : Fin 3} {p : List V} {x y : V}
    (hp : IsRungFrom G A B C i p x y) : 2 ≤ p.length :=
  two_le_length_of_ends_ne hp.2.2.1 (rung_ends_ne hH hp)

theorem rung_one_le_pathLength (hH : IsHyperprism G A B C) {i : Fin 3} {p : List V}
    {x y : V} (hp : IsRungFrom G A B C i p x y) : 1 ≤ SPGT.pathLength p := by
  have := rung_two_le_length hH hp
  simp only [SPGT.pathLength]
  omega

/-- Every vertex of an `i`-rung lies in `Sᵢ = Aᵢ ∪ Bᵢ ∪ Cᵢ`. -/
theorem rung_mem_S {i : Fin 3} {p : List V} {x y : V}
    (hp : IsRungFrom G A B C i p x y) : ∀ v ∈ p, v ∈ A i ∪ B i ∪ C i := by
  obtain ⟨hx, hy, hpath, hint⟩ := hp
  intro v hv
  by_cases hvx : v = x
  · exact Or.inl (Or.inl (by rw [hvx]; exact hx))
  by_cases hvy : v = y
  · exact Or.inl (Or.inr (by rw [hvy]; exact hy))
  · exact Or.inr (hint v ((PathBasics.mem_interior_iff_of_pathFrom hpath).mpr ⟨hv, hvx, hvy⟩))

theorem rung_subset_hyperVerts {i : Fin 3} {p : List V} {x y : V}
    (hp : IsRungFrom G A B C i p x y) : ∀ v ∈ p, v ∈ hyperVerts A B C :=
  fun v hv => subset_hyperVerts i (rung_mem_S hp v hv)

/-- A vertex of an `i`-rung that lies in `Aᵢ` is its `A`-end. -/
theorem rung_eq_A (hH : IsHyperprism G A B C) {i : Fin 3} {p : List V} {x y v : V}
    (hp : IsRungFrom G A B C i p x y) (hv : v ∈ p) (hvA : v ∈ A i) : v = x := by
  obtain ⟨hx, hy, hpath, hint⟩ := hp
  by_cases hvx : v = x
  · exact hvx
  exfalso
  by_cases hvy : v = y
  · have hvB : v ∈ B i := by rw [hvy]; exact hy
    exact dl (hH.2.1 i i) hvA hvB
  · have hmem : v ∈ SPGT.interior p :=
      (PathBasics.mem_interior_iff_of_pathFrom hpath).mpr ⟨hv, hvx, hvy⟩
    exact dl (hH.2.2.1 i i) hvA (hint v hmem)

/-- A vertex of an `i`-rung that lies in `Bᵢ` is its `B`-end. -/
theorem rung_eq_B (hH : IsHyperprism G A B C) {i : Fin 3} {p : List V} {x y v : V}
    (hp : IsRungFrom G A B C i p x y) (hv : v ∈ p) (hvB : v ∈ B i) : v = y := by
  obtain ⟨hx, hy, hpath, hint⟩ := hp
  by_cases hvy : v = y
  · exact hvy
  exfalso
  by_cases hvx : v = x
  · have hvA : v ∈ A i := by rw [hvx]; exact hx
    exact dl (hH.2.1 i i) hvA hvB
  · have hmem : v ∈ SPGT.interior p :=
      (PathBasics.mem_interior_iff_of_pathFrom hpath).mpr ⟨hv, hvx, hvy⟩
    exact dl (hH.2.2.2.1 i i) hvB (hint v hmem)

/-! ### Two rungs of different indices -/

/-- Rungs with different indices are vertex-disjoint. -/
theorem rung_disj (hH : IsHyperprism G A B C) {i j : Fin 3} (hij : i ≠ j)
    {P Q : List V} {x y z w : V}
    (hP : IsRungFrom G A B C i P x y) (hQ : IsRungFrom G A B C j Q z w) :
    ∀ u ∈ P, u ∉ Q :=
  fun u hu hcon => notMem_S hH hij (rung_mem_S hP u hu) (rung_mem_S hQ u hcon)

/-- **The exact adjacency pattern between two rungs of different indices**: the only edges
are the two joining the `A`-ends and the `B`-ends. -/
theorem rung_cross (hH : IsHyperprism G A B C) {i j : Fin 3} (hij : i ≠ j)
    {P Q : List V} {x y z w : V}
    (hP : IsRungFrom G A B C i P x y) (hQ : IsRungFrom G A B C j Q z w) :
    ∀ u ∈ P, ∀ v ∈ Q, (G.Adj u v ↔ (u = x ∧ v = z) ∨ (u = y ∧ v = w)) := by
  intro u hu v hv
  constructor
  · intro hadj
    rcases cross hH hij (rung_mem_S hP u hu) (rung_mem_S hQ v hv) hadj with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨rung_eq_A hH hP hu h1, rung_eq_A hH hQ hv h2⟩
    · exact Or.inr ⟨rung_eq_B hH hP hu h1, rung_eq_B hH hQ hv h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rw [h1, h2]; exact complete_A hH hij _ hP.1 _ hQ.1
    · rw [h1, h2]; exact complete_B hH hij _ hP.2.1 _ hQ.2.1

/-- **Two rungs of different indices close into a hole.**  This is the engine behind claim
(1) of the printed proof, and behind every *"… is an odd hole, a contradiction"* in it. -/
theorem rung_pair_hole (hH : IsHyperprism G A B C) {i j : Fin 3} (hij : i ≠ j)
    {P Q : List V} {x y z w : V}
    (hP : IsRungFrom G A B C i P x y) (hQ : IsRungFrom G A B C j Q z w) :
    IsHoleList G (P ++ Q.reverse) := by
  have hPlen : 2 ≤ P.length := rung_two_le_length hH hP
  have hQlen : 2 ≤ Q.length := rung_two_le_length hH hQ
  refine PathGlue.glue_hole hP.2.2.1 (PathBasics.isPathFrom_reverse hQ.2.2.1) ?_ ?_ ?_
  · intro u hu hcon
    exact rung_disj hH hij hP hQ u hu (List.mem_reverse.mp hcon)
  · intro u hu v hv
    rw [rung_cross hH hij hP hQ u hu v (List.mem_reverse.mp hv)]
    exact or_comm
  · simp only [List.length_reverse]
    omega

/-- Two rungs of different indices have lengths of the same parity. -/
theorem even_pathLength_add (hG : Berge G) (hH : IsHyperprism G A B C) {i j : Fin 3}
    (hij : i ≠ j) {P Q : List V} {x y z w : V}
    (hP : IsRungFrom G A B C i P x y) (hQ : IsRungFrom G A B C j Q z w) :
    Even (SPGT.pathLength P + SPGT.pathLength Q) := by
  have hhole : Even ((P ++ Q.reverse).length) := hG.1 _ (rung_pair_hole hH hij hP hQ)
  simp only [List.length_append, List.length_reverse] at hhole
  have hPl : P.length = SPGT.pathLength P + 1 :=
    PathBasics.length_eq_pathLength_add_one hP.2.2.1.1
  have hQl : Q.length = SPGT.pathLength Q + 1 :=
    PathBasics.length_eq_pathLength_add_one hQ.2.2.1.1
  rw [hPl, hQl] at hhole
  rw [Nat.even_iff] at hhole ⊢
  omega

/-! ### Existence of rungs -/

theorem exists_rung_through (hH : IsHyperprism G A B C) (i : Fin 3) {v : V}
    (hv : v ∈ A i ∪ B i ∪ C i) :
    ∃ (p : List V) (x y : V), IsRungFrom G A B C i p x y ∧ v ∈ p := by
  obtain ⟨p, hp, hvp⟩ := hH.2.2.2.2.2.2.2.2.1 i v hv
  obtain ⟨x, y, hxy⟩ := hp
  exact ⟨p, x, y, hxy, hvp⟩

theorem exists_rung (hH : IsHyperprism G A B C) (i : Fin 3) :
    ∃ (p : List V) (x y : V), IsRungFrom G A B C i p x y := by
  obtain ⟨v, hv⟩ := (hH.1 i).1
  obtain ⟨p, x, y, hxy, _⟩ := exists_rung_through hH i (Or.inl (Or.inl hv))
  exact ⟨p, x, y, hxy⟩

theorem exists_even_zero_rung (hH : IsHyperprism G A B C) :
    ∃ (p : List V) (x y : V), IsRungFrom G A B C 0 p x y ∧ Even (SPGT.pathLength p) := by
  obtain ⟨p, hp, hev⟩ := hH.2.2.2.2.2.2.2.2.2
  obtain ⟨x, y, hxy⟩ := hp
  exact ⟨p, x, y, hxy, hev⟩

/-! ### Claim (1) of the printed proof -/

/-- **Claim (1)** (printed p. 60): *"For `1 ≤ i ≤ 3`, all `i`-rungs have even length.  For we
are given that some 1-rung `R₁` say has even length.  Let `R₂` be a 2-rung; then the union of
`R₁` and `R₂` induces a hole, and so `R₂` is even.  Hence every 2- or 3-rung is even, and
hence so is every 1-rung."* -/
theorem rung_even (hG : Berge G) (hH : IsHyperprism G A B C) {i : Fin 3} {p : List V}
    {x y : V} (hp : IsRungFrom G A B C i p x y) : Even (SPGT.pathLength p) := by
  obtain ⟨q, u, v, hq, hqev⟩ := exists_even_zero_rung hH
  by_cases hi : i = 0
  · -- `p` is a 1-rung: compare it with a 2-rung, which is even by comparison with `q`.
    subst hi
    obtain ⟨r, s, t, hr⟩ := exists_rung hH 1
    have h1 : Even (SPGT.pathLength q + SPGT.pathLength r) :=
      even_pathLength_add hG hH (by decide) hq hr
    have h2 : Even (SPGT.pathLength p + SPGT.pathLength r) :=
      even_pathLength_add hG hH (by decide) hp hr
    rw [Nat.even_iff] at h1 h2 hqev ⊢
    omega
  · have h1 : Even (SPGT.pathLength q + SPGT.pathLength p) :=
      even_pathLength_add hG hH (fun h => hi h.symm) hq hp
    rw [Nat.even_iff] at h1 hqev ⊢
    omega

/-! ### Three rungs form a prism -/

/-- **Three rungs, one of each index, form a prism.**  This is what lets 10.3 and 10.5 be
cited inside the proof of 10.6, and it is what produces the even prism in its last line. -/
theorem rungs_formPrism (hH : IsHyperprism G A B C) {a b : Fin 3 → V} {R : Fin 3 → List V}
    (hR : ∀ i, IsRungFrom G A B C i (R i) (a i) (b i)) :
    FormPrism G a b (R 0) (R 1) (R 2) := by
  refine ⟨?_, ?_, ?_, (hR 0).2.2.1, (hR 1).2.2.1, (hR 2).2.2.1, ?_, ?_, ?_⟩
  · intro i j hij
    exact complete_A hH hij _ (hR i).1 _ (hR j).1
  · intro i j hij
    exact complete_B hH hij _ (hR i).2.1 _ (hR j).2.1
  · intro i j hcon
    have hmem : a i ∈ B j := by rw [hcon]; exact (hR j).2.1
    exact dl (hH.2.1 i j) (hR i).1 hmem
  · exact rung_cross hH (by decide) (hR 0) (hR 1)
  · exact rung_cross hH (by decide) (hR 0) (hR 2)
  · exact rung_cross hH (by decide) (hR 1) (hR 2)

/-- Three rungs, one of each index, form an **even** prism (using claim (1)). -/
theorem rungs_isEvenPrism (hG : Berge G) (hH : IsHyperprism G A B C) {a b : Fin 3 → V}
    {R : Fin 3 → List V} (hR : ∀ i, IsRungFrom G A B C i (R i) (a i) (b i)) :
    IsEvenPrism G a b (R 0) (R 1) (R 2) :=
  ⟨rungs_formPrism hH hR, rung_even hG hH (hR 0), rung_even hG hH (hR 1),
    rung_even hG hH (hR 2)⟩

end Workspace.ProofLemmas.HyperprismBasics
