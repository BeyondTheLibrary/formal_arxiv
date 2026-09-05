import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks

/-!
# Closed walks in a bipartite graph are even, and the parity axiom of a strip system

The final axiom of a `J`-strip system (printed p. 39) reads

> *"For each `uv ∈ E(J)` there is a special `uv`-rung such that for every cycle `C` of `J`, the
> sum of the lengths of the special `uv`-rungs for `uv ∈ E(C)` has the same parity as `|V(C)|`."*

and the paper's justification for it (the remark after 8.1, printed p. 40) is one word: the rungs
come from the tracks of a **bipartite** subdivision `H` of `J`, and going round a cycle of `J`
concatenates those tracks into a *closed walk* of `H`, which in a bipartite graph is even.

This module supplies exactly that, in three steps.

* `exists_walk_of_isTrackFrom` — a track of `H` from `a` to `b`, which in this project is a list
  of vertices, gives a `SimpleGraph.Walk` from `a` to `b` of the same length.  (The list encoding
  and Mathlib's inductive `Walk` have to be bridged once.)
* `even_length_of_isBipartite` — Mathlib already knows the headline fact, as
  `SimpleGraph.two_colorable_iff_forall_loop_even`; `SimpleGraph.IsBipartite` is by definition
  `Colorable 2`, so this is a repackaging, not a reproof.
* `even_sum_trackLength_cycle` / `sum_trackLength_pred_modEq` — the form §8 uses: for **any**
  closed sequence of edges of `J` (the pairs `c.zip (c.rotate 1)` of the paper's cycle `C`), the
  sum of the lengths of the corresponding tracks of `H` is even, hence the sum of the rung
  lengths — one less than the track lengths, by `TrackToRungPath.trackRung_pathLength` — has the
  same parity as `|V(C)| = c.length`.

The proof of the last step does not go through a concatenated walk at all: it is the same
argument in `ZMod 2`.  Fix a two-colouring `col` of `H`; a track has even length exactly when its
two ends get the same colour, so the length of the `uv`-track is `γ u + γ v` in `ZMod 2`, where
`γ u` is the colour of `ι u`.  Summing over `c.zip (c.rotate 1)` gives `Σ γ + Σ γ ∘ rotate`, and
rotating a list permutes it, so the two sums agree and the total is `2 Σ γ = 0`.  This avoids
having to build the concatenation and to know that `c` really is a cycle: no `Nodup` and no
length hypothesis on `c` is needed.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.BipartiteClosedWalkEven

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT

variable {U W : Type*}

/-! ### From the list encoding of a track to a `SimpleGraph.Walk` -/

/-- A list whose consecutive entries are adjacent gives a walk between its two ends, of length
one less than the number of entries.  (Only the adjacency chain is used; `Nodup` plays no role
here, so this applies to any track.) -/
theorem exists_walk_of_chain (H : SimpleGraph W) :
    ∀ (q : List W) (a b : W), q.head? = some a → q.getLast? = some b →
      (∀ i : ℕ, (h : i + 1 < q.length) → H.Adj (q[i]'(by omega)) (q[i + 1]'h)) →
      ∃ w : H.Walk a b, w.length = q.length - 1 := by
  intro q
  induction q with
  | nil => intro a b ha _ _; simp at ha
  | cons x t ih =>
    intro a b ha hb hadj
    have hax : a = x := by simpa using ha.symm
    subst hax
    cases t with
    | nil =>
      have hba : b = a := by simpa using hb.symm
      subst hba
      exact ⟨SimpleGraph.Walk.nil, by simp⟩
    | cons y t' =>
      have h0 : H.Adj a y := by
        have h := hadj 0 (by simp)
        simpa using h
      have hchain : ∀ i : ℕ, (h : i + 1 < (y :: t').length) →
          H.Adj ((y :: t')[i]'(by omega)) ((y :: t')[i + 1]'h) := by
        intro i hi
        have h := hadj (i + 1) (by simp at hi ⊢; omega)
        simpa using h
      obtain ⟨w', hw'⟩ := ih y b (by simp) (by simpa using hb) hchain
      exact ⟨SimpleGraph.Walk.cons h0 w', by simp [hw']⟩

/-- A track of `H` from `a` to `b`, as a walk of `H` from `a` to `b` of length
`trackLength q`. -/
theorem exists_walk_of_isTrackFrom {H : SimpleGraph W} {q : List W} {a b : W}
    (h : IsTrackFrom H q a b) : ∃ w : H.Walk a b, w.length = trackLength q := by
  obtain ⟨⟨-, -, hadj⟩, hh, hl⟩ := h
  simpa [trackLength] using exists_walk_of_chain H q a b hh hl hadj

/-! ### Bipartite graphs have no odd closed walk (Mathlib) -/

/-- **In a bipartite graph every closed walk has even length.**  `SimpleGraph.IsBipartite` is
`Colorable 2`, so this is Mathlib's `two_colorable_iff_forall_loop_even`. -/
theorem even_length_of_isBipartite {H : SimpleGraph W} (hbip : H.IsBipartite) (u : W)
    (w : H.Walk u u) : Even w.length :=
  SimpleGraph.two_colorable_iff_forall_loop_even.mp hbip u w

/-- A two-colouring of `H`, as a `Bool`-colouring, exists whenever `H` is bipartite. -/
theorem exists_boolColoring_of_isBipartite {H : SimpleGraph W} (hbip : H.IsBipartite) :
    Nonempty (H.Coloring Bool) :=
  ⟨H.recolorOfEquiv finTwoEquiv hbip.some⟩

/-- **A track is even exactly when its two ends get the same colour.** -/
theorem even_trackLength_iff {H : SimpleGraph W} (col : H.Coloring Bool) {q : List W} {a b : W}
    (h : IsTrackFrom H q a b) : Even (trackLength q) ↔ col a = col b := by
  obtain ⟨w, hw⟩ := exists_walk_of_isTrackFrom h
  have h1 : Even w.length ↔ (col a = true ↔ col b = true) :=
    SimpleGraph.Coloring.even_length_iff_congr col w
  rw [← hw, h1]
  cases hca : col a <;> cases hcb : col b <;> simp

/-! ### Summing round a cycle -/

/-- The length of a track, in `ZMod 2`, is the sum of the colours of its two ends. -/
private theorem cast_trackLength_eq {H : SimpleGraph W} (col : H.Coloring Bool)
    {q : List W} {a b : W} (h : IsTrackFrom H q a b) :
    ((trackLength q : ℕ) : ZMod 2)
      = (if col a = true then 1 else 0) + (if col b = true then 1 else 0) := by
  have hpar := even_trackLength_iff col h
  have hz : ∀ x y : ZMod 2, (x = 0 ↔ y = 0) → x = y := by decide
  refine hz _ _ ?_
  rw [ZMod.natCast_eq_zero_iff_even, hpar]
  cases hca : col a <;> cases hcb : col b <;> simp <;> decide

private theorem cast_sum_map {α : Type*} (L : List α) (f : α → ℕ) :
    (((L.map f).sum : ℕ) : ZMod 2) = (L.map fun x => ((f x : ℕ) : ZMod 2)).sum := by
  induction L with
  | nil => simp
  | cons a t ih => simp [ih]

private theorem sum_map_add {α M : Type*} [AddCommMonoid M] (L : List α) (f g : α → M) :
    (L.map fun x => f x + g x).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; abel

/-- **The parity fact §8's last axiom needs.**  Let `H` be a bipartite subdivision of `J`, with
embedding `ι` of `V(J)` and tracks `T u v`.  Then for any closed sequence of edges of `J` — in
particular for the edges `c.zip (c.rotate 1)` of a cycle `C` of `J` with vertex list `c` — the
sum of the lengths of the corresponding tracks of `H` is even.

(Concatenating the tracks round the cycle is a closed walk of `H`; `H` is bipartite; done.  The
proof below runs the same parity bookkeeping in `ZMod 2`, which is why neither `c.Nodup` nor
`3 ≤ c.length` has to be assumed.) -/
theorem even_sum_trackLength_cycle {J : SimpleGraph U} {H : SimpleGraph W}
    (hbip : H.IsBipartite) {ι : U → W} {T : U → U → List W}
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v))
    (c : List U) (hadj : ∀ p ∈ c.zip (c.rotate 1), J.Adj p.1 p.2) :
    Even (((c.zip (c.rotate 1)).map fun p => trackLength (T p.1 p.2)).sum) := by
  classical
  obtain ⟨col⟩ := exists_boolColoring_of_isBipartite hbip
  set γ : U → ZMod 2 := fun u => if col (ι u) = true then 1 else 0 with hγ
  set L : List (U × U) := c.zip (c.rotate 1) with hL
  -- each track length is `γ u + γ v` in `ZMod 2`
  have hstep : ∀ p ∈ L, ((trackLength (T p.1 p.2) : ℕ) : ZMod 2) = γ p.1 + γ p.2 := by
    intro p hp
    exact cast_trackLength_eq col (htrack p.1 p.2 (hadj p hp))
  -- so the whole sum is `Σ γ ∘ fst + Σ γ ∘ snd`
  have hcast : (((L.map fun p => trackLength (T p.1 p.2)).sum : ℕ) : ZMod 2)
      = (L.map fun p => γ p.1 + γ p.2).sum := by
    rw [cast_sum_map]
    exact congrArg List.sum (List.map_congr_left hstep)
  have hfst : (L.map fun p : U × U => γ p.1) = c.map γ := by
    have h1 : List.map Prod.fst L = c :=
      List.map_fst_zip (by simp [hL])
    calc (L.map fun p : U × U => γ p.1) = (List.map Prod.fst L).map γ := by
          simp [List.map_map, Function.comp]
      _ = c.map γ := by rw [h1]
  have hsnd : (L.map fun p : U × U => γ p.2) = (c.rotate 1).map γ := by
    have h1 : List.map Prod.snd L = c.rotate 1 :=
      List.map_snd_zip (by simp [hL])
    calc (L.map fun p : U × U => γ p.2) = (List.map Prod.snd L).map γ := by
          simp [List.map_map, Function.comp]
      _ = (c.rotate 1).map γ := by rw [h1]
  have hperm : ((c.rotate 1).map γ).sum = (c.map γ).sum :=
    List.Perm.sum_eq (List.Perm.map γ (c.rotate_perm 1))
  have hzero : (((L.map fun p => trackLength (T p.1 p.2)).sum : ℕ) : ZMod 2) = 0 := by
    rw [hcast, sum_map_add, hfst, hsnd, hperm]
    have hself : ∀ x : ZMod 2, x + x = 0 := by decide
    exact hself _
  exact ZMod.natCast_eq_zero_iff_even.mp hzero

/-! ### The form the strip-system axiom is stated in -/

private theorem sum_map_pred (L : List ℕ) (h : ∀ x ∈ L, 1 ≤ x) :
    (L.map fun x => x - 1).sum + L.length = L.sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    have ha : 1 ≤ a := h a (by simp)
    have ih' := ih fun x hx => h x (by simp [hx])
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- **The parity clause of a `J`-strip system, read off the tracks.**  With rungs of length
`trackLength (T u v) - 1` (which is what `TrackToRungPath.trackRung_pathLength` gives), the sum
of the rung lengths round a cycle `c` of `J` is congruent to `|V(C)| = c.length` mod `2`. -/
theorem sum_trackLength_pred_modEq {J : SimpleGraph U} {H : SimpleGraph W}
    (hbip : H.IsBipartite) {ι : U → W} {T : U → U → List W}
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v))
    (hlen : ∀ u v : U, J.Adj u v → 1 ≤ trackLength (T u v))
    (c : List U) (hadj : ∀ p ∈ c.zip (c.rotate 1), J.Adj p.1 p.2) :
    (((c.zip (c.rotate 1)).map fun p => trackLength (T p.1 p.2) - 1)).sum
      ≡ c.length [MOD 2] := by
  classical
  set L : List (U × U) := c.zip (c.rotate 1) with hL
  set M : List ℕ := L.map fun p => trackLength (T p.1 p.2) with hM
  have hMpos : ∀ x ∈ M, 1 ≤ x := by
    intro x hx
    rw [hM] at hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact hlen p.1 p.2 (hadj p hp)
  have hMlen : M.length = c.length := by
    simp [hM, hL]
  have hsum : (M.map fun x => x - 1).sum + M.length = M.sum := sum_map_pred M hMpos
  have hmap : (M.map fun x => x - 1) = L.map fun p => trackLength (T p.1 p.2) - 1 := by
    simp [hM, List.map_map, Function.comp]
  have heven : Even M.sum := even_sum_trackLength_cycle hbip htrack c hadj
  rw [Nat.even_iff] at heven
  rw [hmap, hMlen] at hsum
  unfold Nat.ModEq
  omega

end Workspace.ProofLemmas.BipartiteClosedWalkEven
