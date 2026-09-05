import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics

/-!
# Closing paths into holes, and assembling prisms

Shared infrastructure for the section proofs.  Nothing here corresponds to a
numbered result of the paper; these are the two constructions that every section
otherwise re-derives by hand.

## (a) Closing a path into a hole

The single most repeated move in the paper is *"… so `x-P-y-v-x` is a hole of
length `k`, a contradiction"*: a path `P` from `u` to `v`, together with one
further vertex `w` adjacent to `u` and to `v` and to nothing else of `P`, is a
hole.  In the list encoding the hole is simply `w :: p`, so the length
bookkeeping is `holeLength (w :: p) = pathLength p + 2` and the parity a caller
wants falls straight out of `Berge`.

Because the ambient graph is arbitrary, instantiating at `Gᶜ` gives the
antipath/antihole mirror for free — `HoleBasics.berge_compl` turns `Berge G` into
`Berge Gᶜ` in one step.  Both instances are provided.

## (b) Assembling a prism

`Workspace.Types.Prisms.SPGT.FormPrism` is indexed by `Fin 3`.  A section proof
always has the six triangle vertices and the three paths under *individual*
names, so `formPrism_of_data` takes them that way and does the `![·,·,·]`
packaging; the `*_of_formPrism` lemmas then wrap a `FormPrism` into whichever of
`IsPrism` / `IsLongPrism` / `IsEvenPrism` / `IsOddPrism` the ambient
`InF3`/`InF4`/`InF5` hypothesis is waiting to be contradicted by.
-/

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.PrismBasics

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT

variable {V : Type*}

/-! ### Destructuring a list of known small length

The paper constantly says *"let its vertices be `p₁-⋯-p_k` in order"*.  Turning
the list into a literal is what makes `SPGT.interior [x0, x1, x2, x3] = [x1, x2]`
a plain `rfl`. -/

theorem length_eq_two {α : Type*} {l : List α} (h : l.length = 2) :
    ∃ a b, l = [a, b] := by
  match l, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

theorem length_eq_three {α : Type*} {l : List α} (h : l.length = 3) :
    ∃ a b c, l = [a, b, c] := by
  match l, h with
  | [a, b, c], _ => exact ⟨a, b, c, rfl⟩

theorem length_eq_four {α : Type*} {l : List α} (h : l.length = 4) :
    ∃ a b c d, l = [a, b, c, d] := by
  match l, h with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

theorem length_eq_five {α : Type*} {l : List α} (h : l.length = 5) :
    ∃ a b c d e, l = [a, b, c, d, e] := by
  match l, h with
  | [a, b, c, d, e], _ => exact ⟨a, b, c, d, e, rfl⟩

theorem length_eq_six {α : Type*} {l : List α} (h : l.length = 6) :
    ∃ a b c d e f, l = [a, b, c, d, e, f] := by
  match l, h with
  | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩

/-! ### Constructing an `IsHoleList`

`IsHoleList` states adjacency as an `↔` over *all* pairs of indices; since
adjacency is symmetric it is enough to check the pairs with `i ≤ j`, which halves
every case bash.  And `omega` cannot handle a `%` with a variable modulus, so the
cyclic-successor test has to be turned into plain arithmetic first. -/

/-- A list of at least four distinct vertices whose adjacencies are the cyclically
consecutive pairs *for indices `i ≤ j`* is a hole: the remaining pairs follow by
symmetry of adjacency. -/
theorem isHoleList_of_le {G : SimpleGraph V} {l : List V}
    (h4 : 4 ≤ l.length) (hnd : l.Nodup)
    (hadj : ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length), i ≤ j →
      (G.Adj (l[i]'hi) (l[j]'hj) ↔ (j = (i + 1) % l.length ∨ i = (j + 1) % l.length))) :
    IsHoleList G l := by
  refine ⟨h4, hnd, ?_⟩
  intro i j hi hj
  rcases le_total i j with h | h
  · exact hadj i j hi hj h
  · rw [SimpleGraph.adj_comm, hadj j i hj hi h]
    tauto

/-- On a cycle of length `n + 1`, for indices `i ≤ j ≤ n`, being cyclically
consecutive means `j = i + 1` or (the wrap-around) `i = 0` and `j = n`.  This is
what removes the variable-modulus `%` that `omega` cannot see through. -/
theorem cyc_rhs {n i j : ℕ} (hn : 1 ≤ n) (hi : i ≤ n) (hj : j ≤ n) (hij : i ≤ j) :
    (j = (i + 1) % (n + 1) ∨ i = (j + 1) % (n + 1)) ↔ (j = i + 1 ∨ (i = 0 ∧ j = n)) := by
  have h1 : (i + 1) % (n + 1) = if i = n then 0 else i + 1 := by
    by_cases h : i = n
    · simp [h]
    · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]
  have h2 : (j + 1) % (n + 1) = if j = n then 0 else j + 1 := by
    by_cases h : j = n
    · simp [h]
    · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]
  rw [h1, h2]
  split_ifs <;> omega

/-! ### Closing a path into a hole through one extra vertex -/

/-- **Closing a path into a hole.**  If `p` is a path from `u` to `v` of length at
least `2`, and `w` is a vertex outside `p` adjacent to both ends of `p` and to no
interior vertex of `p`, then `w :: p` is a hole — the paper's `w-u-P-v-w`.

The hypothesis `2 ≤ pathLength p` is exactly what makes the resulting cycle have
the four vertices a hole needs. -/
theorem isHoleList_of_path_add_vertex {G : SimpleGraph V} {p : List V} {u v w : V}
    (hp : IsPathFrom G p u v) (hlen : 2 ≤ pathLength p)
    (hwu : G.Adj w u) (hwv : G.Adj w v) (hw : w ∉ p)
    (hwint : ∀ x ∈ SPGT.interior p, ¬ G.Adj w x) :
    IsHoleList G (w :: p) := by
  obtain ⟨hpl, hhd, hlst⟩ := hp
  have hpos : 0 < p.length := PathBasics.path_length_pos hpl
  have hn3 : 3 ≤ p.length := by
    have := PathBasics.pathLength_eq p
    omega
  have h0 : p[0]'hpos = u := PathBasics.getElem_zero_of_head? hhd hpos
  have hlast : p[p.length - 1]'(by omega) = v :=
    PathBasics.getElem_last_of_getLast? hlst hpos
  refine isHoleList_of_le (by simp only [List.length_cons]; omega)
    (List.nodup_cons.mpr ⟨hw, PathBasics.path_nodup hpl⟩) ?_
  intro i j hi hj hij
  have hi' : i < p.length + 1 := by simpa using hi
  have hj' : j < p.length + 1 := by simpa using hj
  have key : (j = (i + 1) % (w :: p).length ∨ i = (j + 1) % (w :: p).length)
      ↔ (j = i + 1 ∨ (i = 0 ∧ j = p.length)) :=
    cyc_rhs (n := p.length) (by omega) (by omega) (by omega) hij
  rw [key]
  by_cases hi0 : i = 0
  · subst hi0
    by_cases hj0 : j = 0
    · subst hj0
      simp only [List.getElem_cons_zero]
      exact iff_of_false G.irrefl (by omega)
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hjp : j' < p.length := by omega
      simp only [List.getElem_cons_zero, List.getElem_cons_succ]
      by_cases hj1 : j' = 0
      · subst hj1
        rw [h0]
        exact iff_of_true hwu (Or.inl (by trivial))
      · by_cases hjl : j' = p.length - 1
        · subst hjl
          rw [hlast]
          exact iff_of_true hwv (Or.inr ⟨trivial, by omega⟩)
        · refine iff_of_false ?_ (by omega)
          exact hwint _ (PathBasics.getElem_mem_interior hpl hjp (by omega) (by omega))
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hip : i' < p.length := by omega
    have hjp : j' < p.length := by omega
    simp only [List.getElem_cons_succ]
    rw [PathBasics.path_adj_iff hpl hip hjp]
    omega

/-- Length bookkeeping for `isHoleList_of_path_add_vertex`: closing a path of
length `ℓ` through one extra vertex produces a hole of length `ℓ + 2`.  A caller
reads the parity off this. -/
theorem holeLength_cons (w : V) {p : List V} (hp : p ≠ []) :
    holeLength (w :: p) = pathLength p + 2 := by
  have : 0 < p.length := List.length_pos_of_ne_nil hp
  simp only [holeLength, pathLength, List.length_cons]
  omega

/-- The witness-carrying form of `isHoleList_of_path_add_vertex`, for callers that
need the hole itself (its length, and its vertex set) rather than just its
parity. -/
theorem isHoleList_closeWith {G : SimpleGraph V} {p : List V} {u v w : V}
    (hp : IsPathFrom G p u v) (hlen : 2 ≤ pathLength p)
    (hwu : G.Adj w u) (hwv : G.Adj w v) (hw : w ∉ p)
    (hwint : ∀ x ∈ SPGT.interior p, ¬ G.Adj w x) :
    ∃ c : List V, IsHoleList G c ∧ holeLength c = pathLength p + 2 ∧
      ∀ y : V, y ∈ c ↔ (y = w ∨ y ∈ p) :=
  ⟨w :: p, isHoleList_of_path_add_vertex hp hlen hwu hwv hw hwint,
    holeLength_cons w (PathBasics.path_ne_nil hp.1), fun _ => List.mem_cons⟩

/-- **The parity consequence, in a Berge graph.**  A path `q` on at least four
vertices whose two ends — and no interior vertex — are adjacent to some vertex
`x` outside `q` closes into a hole, so `q.length + 1` is even.

Because `G` is arbitrary this instantiates at `Gᶜ` to give the antipath/antihole
version (*"`Q` cannot be completed to an odd antihole via `p₃-v-p₂`"*); see
`even_of_antipath_closed_by_vertex`. -/
theorem even_of_path_closed_by_vertex {G : SimpleGraph V} {q : List V} {u w x : V}
    (hG : Berge G) (hq : IsPathFrom G q u w) (h4 : 4 ≤ q.length) (hx : x ∉ q)
    (hxu : G.Adj x u) (hxw : G.Adj x w)
    (hxint : ∀ y ∈ SPGT.interior q, ¬ G.Adj x y) :
    Even (q.length + 1) := by
  have hhole : IsHoleList G (x :: q) :=
    isHoleList_of_path_add_vertex hq
      (by have := PathBasics.pathLength_eq q; omega) hxu hxw hx hxint
  simpa [holeLength] using hG.1 _ hhole

/-! ### The antipath / antihole mirror

An antipath of `G` is a path of `Gᶜ` and an antihole of `G` is a hole of `Gᶜ`, so
each statement above transfers by instantiating at `Gᶜ`; `HoleBasics.berge_compl`
supplies `Berge Gᶜ`. -/

/-- The antipath mirror of `isHoleList_of_path_add_vertex`. -/
theorem isAntiholeList_of_antipath_add_vertex {G : SimpleGraph V} {p : List V} {u v w : V}
    (hp : IsAntipathFrom G p u v) (hlen : 2 ≤ pathLength p)
    (hwu : Gᶜ.Adj w u) (hwv : Gᶜ.Adj w v) (hw : w ∉ p)
    (hwint : ∀ x ∈ SPGT.interior p, ¬ Gᶜ.Adj w x) :
    IsAntiholeList G (w :: p) :=
  isHoleList_of_path_add_vertex hp hlen hwu hwv hw hwint

/-- The antipath mirror of `even_of_path_closed_by_vertex`, stated with adjacency
in `Gᶜ`. -/
theorem even_of_antipath_closed_by_vertex {G : SimpleGraph V} {q : List V} {u w x : V}
    (hG : Berge G) (hq : IsAntipathFrom G q u w) (h4 : 4 ≤ q.length) (hx : x ∉ q)
    (hxu : Gᶜ.Adj x u) (hxw : Gᶜ.Adj x w)
    (hxint : ∀ y ∈ SPGT.interior q, ¬ Gᶜ.Adj x y) :
    Even (q.length + 1) :=
  even_of_path_closed_by_vertex (HoleBasics.berge_compl.mpr hG) hq h4 hx hxu hxw hxint

/-- The antipath mirror with every hypothesis phrased in `G` itself, which is the
form a section proof actually has: `x` is *non*-adjacent to (and distinct from)
the two ends of the antipath, and *is* adjacent to every interior vertex — the
latter being how "the interior of `Q` lies in `X` and `x` is `X`-complete" is
used. -/
theorem even_of_antipath_closed_by_vertex' {G : SimpleGraph V} {q : List V} {u w x : V}
    (hG : Berge G) (hq : IsAntipathFrom G q u w) (h4 : 4 ≤ q.length) (hx : x ∉ q)
    (hxu : x ≠ u) (hxw : x ≠ w) (hnu : ¬ G.Adj x u) (hnw : ¬ G.Adj x w)
    (hxint : ∀ y ∈ SPGT.interior q, G.Adj x y) :
    Even (q.length + 1) := by
  refine even_of_antipath_closed_by_vertex hG hq h4 hx
    ((G.compl_adj x u).mpr ⟨hxu, hnu⟩) ((G.compl_adj x w).mpr ⟨hxw, hnw⟩) ?_
  intro y hy hadj
  exact ((G.compl_adj x y).mp hadj).2 (hxint y hy)

/-! ### Closing a path into a hole through two extra vertices

The paper's `x-P-y-v-w-x`: the path `p` runs from `u` to `v`, the extra vertex `s`
is attached at `u`, the extra vertex `t` at `v`, and `s`, `t` are adjacent to each
other.  The cycle is `t-s-u-P-v-t`, i.e. the list `t :: s :: p`. -/

/-- Closing a path into a hole through two adjacent extra vertices, one attached
at each end.  Only `1 ≤ pathLength p` is needed: for `p = [u, v]` the result is
the four-vertex hole `t-s-u-v-t`. -/
theorem isHoleList_of_path_add_two_vertices {G : SimpleGraph V} {p : List V} {u v s t : V}
    (hp : IsPathFrom G p u v) (hlen : 1 ≤ pathLength p)
    (hsu : G.Adj s u) (htv : G.Adj t v) (hst : G.Adj s t)
    (hs : s ∉ p) (ht : t ∉ p) (hsv : ¬ G.Adj s v) (htu : ¬ G.Adj t u)
    (hsint : ∀ x ∈ SPGT.interior p, ¬ G.Adj s x)
    (htint : ∀ x ∈ SPGT.interior p, ¬ G.Adj t x) :
    IsHoleList G (t :: s :: p) := by
  obtain ⟨hpl, hhd, hlst⟩ := hp
  have hpos : 0 < p.length := PathBasics.path_length_pos hpl
  have hn2 : 2 ≤ p.length := by
    have := PathBasics.pathLength_eq p
    omega
  have h0 : p[0]'hpos = u := PathBasics.getElem_zero_of_head? hhd hpos
  have hlast : p[p.length - 1]'(by omega) = v :=
    PathBasics.getElem_last_of_getLast? hlst hpos
  refine isHoleList_of_le (by simp only [List.length_cons]; omega) ?_ ?_
  · refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨hs, PathBasics.path_nodup hpl⟩⟩
    intro hmem
    rcases List.mem_cons.mp hmem with h | h
    · exact hst.ne' h
    · exact ht h
  intro i j hi hj hij
  have hi' : i < p.length + 2 := hi
  have hj' : j < p.length + 2 := hj
  have key : (j = (i + 1) % (t :: s :: p).length ∨ i = (j + 1) % (t :: s :: p).length)
      ↔ (j = i + 1 ∨ (i = 0 ∧ j = p.length + 1)) :=
    cyc_rhs (n := p.length + 1) (by omega) (by omega) (by omega) hij
  rw [key]
  by_cases hi0 : i = 0
  · subst hi0
    by_cases hj0 : j = 0
    · subst hj0
      simp only [List.getElem_cons_zero]
      exact iff_of_false G.irrefl (by omega)
    · by_cases hj1 : j = 1
      · subst hj1
        simp only [List.getElem_cons_zero, List.getElem_cons_succ]
        exact iff_of_true hst.symm (Or.inl trivial)
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
        have hjp : j' < p.length := by omega
        simp only [List.getElem_cons_zero, List.getElem_cons_succ]
        by_cases hjl : j' = p.length - 1
        · subst hjl
          rw [hlast]
          exact iff_of_true htv (Or.inr ⟨trivial, by omega⟩)
        · refine iff_of_false ?_ (by omega)
          by_cases hj2 : j' = 0
          · subst hj2
            rw [h0]
            exact htu
          · exact htint _ (PathBasics.getElem_mem_interior hpl hjp (by omega) (by omega))
  · by_cases hi1 : i = 1
    · subst hi1
      by_cases hj1 : j = 1
      · subst hj1
        simp only [List.getElem_cons_succ, List.getElem_cons_zero]
        exact iff_of_false G.irrefl (by omega)
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
        have hjp : j' < p.length := by omega
        simp only [List.getElem_cons_succ, List.getElem_cons_zero]
        by_cases hj2 : j' = 0
        · subst hj2
          rw [h0]
          exact iff_of_true hsu (Or.inl (by trivial))
        · refine iff_of_false ?_ (by omega)
          by_cases hjl : j' = p.length - 1
          · subst hjl
            rw [hlast]
            exact hsv
          · exact hsint _ (PathBasics.getElem_mem_interior hpl hjp (by omega) (by omega))
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by omega⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
      have hip : i' < p.length := by omega
      have hjp : j' < p.length := by omega
      simp only [List.getElem_cons_succ]
      rw [PathBasics.path_adj_iff hpl hip hjp]
      omega

/-- Length bookkeeping for `isHoleList_of_path_add_two_vertices`: closing a path
of length `ℓ` through two extra vertices produces a hole of length `ℓ + 3`. -/
theorem holeLength_cons_cons (s t : V) {p : List V} (hp : p ≠ []) :
    holeLength (t :: s :: p) = pathLength p + 3 := by
  have : 0 < p.length := List.length_pos_of_ne_nil hp
  simp only [holeLength, pathLength, List.length_cons]
  omega

/-! ### Assembling a prism from three paths

`FormPrism` is `Fin 3`-indexed; a section proof always has the six triangle
vertices under individual names.  `formPrism_of_data` does the `![·,·,·]`
packaging once and for all. -/

/-- Assembling `FormPrism` from its presenting data: six vertices forming the two
triangles `{a0, a1, a2}` and `{b0, b1, b2}`, the three paths `P₁, P₂, P₃` with
`Pᵢ` running from `aᵢ` to `bᵢ`, the nine disequalities between the two triangles,
and the three *"the only edges between `V(Pᵢ)` and `V(Pⱼ)` are `aᵢaⱼ` and
`bᵢbⱼ`"* conditions. -/
theorem formPrism_of_data {G : SimpleGraph V}
    {a0 a1 a2 b0 b1 b2 : V} {P₁ P₂ P₃ : List V}
    (ha01 : G.Adj a0 a1) (ha02 : G.Adj a0 a2) (ha12 : G.Adj a1 a2)
    (hb01 : G.Adj b0 b1) (hb02 : G.Adj b0 b2) (hb12 : G.Adj b1 b2)
    (h00 : a0 ≠ b0) (h01 : a0 ≠ b1) (h02 : a0 ≠ b2)
    (h10 : a1 ≠ b0) (h11 : a1 ≠ b1) (h12 : a1 ≠ b2)
    (h20 : a2 ≠ b0) (h21 : a2 ≠ b1) (h22 : a2 ≠ b2)
    (hq1 : IsPathFrom G P₁ a0 b0) (hq2 : IsPathFrom G P₂ a1 b1)
    (hq3 : IsPathFrom G P₃ a2 b2)
    (e12 : ∀ u ∈ P₁, ∀ v ∈ P₂, (G.Adj u v ↔ (u = a0 ∧ v = a1) ∨ (u = b0 ∧ v = b1)))
    (e13 : ∀ u ∈ P₁, ∀ v ∈ P₃, (G.Adj u v ↔ (u = a0 ∧ v = a2) ∨ (u = b0 ∧ v = b2)))
    (e23 : ∀ u ∈ P₂, ∀ v ∈ P₃, (G.Adj u v ↔ (u = a1 ∧ v = a2) ∨ (u = b1 ∧ v = b2))) :
    FormPrism G ![a0, a1, a2] ![b0, b1, b2] P₁ P₂ P₃ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;>
      first
        | exact ha01 | exact ha02 | exact ha12
        | exact ha01.symm | exact ha02.symm | exact ha12.symm
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;>
      first
        | exact hb01 | exact hb02 | exact hb12
        | exact hb01.symm | exact hb02.symm | exact hb12.symm
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      assumption
  · simpa using hq1
  · simpa using hq2
  · simpa using hq3
  · simpa using e12
  · simpa using e13
  · simpa using e23

/-! #### Packaging a `FormPrism` as the object a class hypothesis expects

Sections 7, 10, 11, 12 and 13 all contradict `InF3` / `InF4` / `InF5` by
exhibiting a prism, so these are the shapes those hypotheses ask for. -/

/-- The vertex set of the prism formed by `P₁, P₂, P₃` really is a prism. -/
theorem isPrism_of_formPrism {G : SimpleGraph V} {α β : Fin 3 → V} {P₁ P₂ P₃ : List V}
    (h : FormPrism G α β P₁ P₂ P₃) :
    IsPrism G ({v | v ∈ P₁} ∪ {v | v ∈ P₂} ∪ {v | v ∈ P₃}) :=
  ⟨α, β, P₁, P₂, P₃, h, rfl⟩

theorem exists_isPrism_of_formPrism {G : SimpleGraph V} {α β : Fin 3 → V}
    {P₁ P₂ P₃ : List V} (h : FormPrism G α β P₁ P₂ P₃) :
    ∃ K : Set V, IsPrism G K :=
  ⟨_, isPrism_of_formPrism h⟩

theorem isLongPrism_of_formPrism {G : SimpleGraph V} {α β : Fin 3 → V}
    {P₁ P₂ P₃ : List V} (h : FormPrism G α β P₁ P₂ P₃)
    (hlong : 1 < pathLength P₁ ∨ 1 < pathLength P₂ ∨ 1 < pathLength P₃) :
    IsLongPrism G α β P₁ P₂ P₃ :=
  ⟨h, hlong⟩

theorem exists_isLongPrism_of_formPrism {G : SimpleGraph V} {α β : Fin 3 → V}
    {P₁ P₂ P₃ : List V} (h : FormPrism G α β P₁ P₂ P₃)
    (hlong : 1 < pathLength P₁ ∨ 1 < pathLength P₂ ∨ 1 < pathLength P₃) :
    ∃ (a b : Fin 3 → V) (Q₁ Q₂ Q₃ : List V), IsLongPrism G a b Q₁ Q₂ Q₃ :=
  ⟨α, β, P₁, P₂, P₃, h, hlong⟩

theorem isEvenPrism_of_formPrism {G : SimpleGraph V} {α β : Fin 3 → V}
    {P₁ P₂ P₃ : List V} (h : FormPrism G α β P₁ P₂ P₃)
    (h1 : Even (pathLength P₁)) (h2 : Even (pathLength P₂)) (h3 : Even (pathLength P₃)) :
    IsEvenPrism G α β P₁ P₂ P₃ :=
  ⟨h, h1, h2, h3⟩

theorem exists_isEvenPrism_of_formPrism {G : SimpleGraph V} {α β : Fin 3 → V}
    {P₁ P₂ P₃ : List V} (h : FormPrism G α β P₁ P₂ P₃)
    (h1 : Even (pathLength P₁)) (h2 : Even (pathLength P₂)) (h3 : Even (pathLength P₃)) :
    ∃ (a b : Fin 3 → V) (Q₁ Q₂ Q₃ : List V), IsEvenPrism G a b Q₁ Q₂ Q₃ :=
  ⟨α, β, P₁, P₂, P₃, h, h1, h2, h3⟩

theorem isOddPrism_of_formPrism {G : SimpleGraph V} {α β : Fin 3 → V}
    {P₁ P₂ P₃ : List V} (h : FormPrism G α β P₁ P₂ P₃)
    (hodd : ¬ (Even (pathLength P₁) ∧ Even (pathLength P₂) ∧ Even (pathLength P₃))) :
    IsOddPrism G α β P₁ P₂ P₃ :=
  ⟨h, hodd⟩

theorem exists_isOddPrism_of_formPrism {G : SimpleGraph V} {α β : Fin 3 → V}
    {P₁ P₂ P₃ : List V} (h : FormPrism G α β P₁ P₂ P₃)
    (hodd : ¬ (Even (pathLength P₁) ∧ Even (pathLength P₂) ∧ Even (pathLength P₃))) :
    ∃ (a b : Fin 3 → V) (Q₁ Q₂ Q₃ : List V), IsOddPrism G a b Q₁ Q₂ Q₃ :=
  ⟨α, β, P₁, P₂, P₃, h, hodd⟩

/-- The composite that the proof of 13.6 wanted: presenting data plus a witness
that one of the three paths has length `> 1`, giving a long prism.  This is
`exists_isLongPrism_of_formPrism (formPrism_of_data …) hlong`. -/
theorem formPrism_mk {G : SimpleGraph V}
    {a0 a1 a2 b0 b1 b2 : V} {P₁ P₂ P₃ : List V}
    (ha01 : G.Adj a0 a1) (ha02 : G.Adj a0 a2) (ha12 : G.Adj a1 a2)
    (hb01 : G.Adj b0 b1) (hb02 : G.Adj b0 b2) (hb12 : G.Adj b1 b2)
    (h00 : a0 ≠ b0) (h01 : a0 ≠ b1) (h02 : a0 ≠ b2)
    (h10 : a1 ≠ b0) (h11 : a1 ≠ b1) (h12 : a1 ≠ b2)
    (h20 : a2 ≠ b0) (h21 : a2 ≠ b1) (h22 : a2 ≠ b2)
    (hq1 : IsPathFrom G P₁ a0 b0) (hq2 : IsPathFrom G P₂ a1 b1)
    (hq3 : IsPathFrom G P₃ a2 b2)
    (e12 : ∀ u ∈ P₁, ∀ v ∈ P₂, (G.Adj u v ↔ (u = a0 ∧ v = a1) ∨ (u = b0 ∧ v = b1)))
    (e13 : ∀ u ∈ P₁, ∀ v ∈ P₃, (G.Adj u v ↔ (u = a0 ∧ v = a2) ∨ (u = b0 ∧ v = b2)))
    (e23 : ∀ u ∈ P₂, ∀ v ∈ P₃, (G.Adj u v ↔ (u = a1 ∧ v = a2) ∨ (u = b1 ∧ v = b2)))
    (hlong : 1 < pathLength P₁ ∨ 1 < pathLength P₂ ∨ 1 < pathLength P₃) :
    ∃ (a b : Fin 3 → V) (Q₁ Q₂ Q₃ : List V), IsLongPrism G a b Q₁ Q₂ Q₃ :=
  exists_isLongPrism_of_formPrism
    (formPrism_of_data ha01 ha02 ha12 hb01 hb02 hb12 h00 h01 h02 h10 h11 h12 h20 h21 h22
      hq1 hq2 hq3 e12 e13 e23) hlong

end Workspace.ProofLemmas.PrismBasics
