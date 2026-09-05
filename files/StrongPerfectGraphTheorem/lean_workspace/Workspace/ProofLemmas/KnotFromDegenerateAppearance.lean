import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Knots
import Workspace.ProofLemmas.DegenerateK4Tracks

/-!
# A degenerate appearance of `K₄` can be viewed as a knot

This module supplies the §9 preamble sentence (printed p. 47), the one the proof of 9.6
invokes with *"By hypothesis it is degenerate, and hence there is a striation in `G`"*:

> *"If `L(H)` is a degenerate appearance of `K₄` in `G`, it can be viewed as a knot.  For, in
> our usual notation, let `R_{1,3}, R_{1,4}, R_{2,3}, R_{2,4}` have length 0; let `P₁ = R_{1,2}`,
> `P₂ = R_{3,4}`, let `Q₁` be the antipath `r_{1,3}-r_{2,4}`, and `Q₂` the antipath
> `r_{1,4}-r_{2,3}`.  It is easy to check that this is a knot."*

## The construction

`DegenerateK4Tracks.exists_two_tracks_of_degenerate` turns the degenerate bipartite
subdivision `H` of `K₄` into two vertex-disjoint tracks `p₁-⋯-p_m` and `q₁-⋯-q_k` of `H`,
with `m, k ≥ 3` odd, such that the four *cross edges*

```
u₁ = p₁q₁      u₂ = p₁q_k      u₃ = p_mq₁      u₄ = p_mq_k
```

are edges of `H`.  These are the paper's `R_{1,3}, R_{1,4}, R_{2,3}, R_{2,4}` "of length 0":
in the line graph they are single vertices.  Transporting the edges of `H` to vertices of `G`
along the appearance isomorphism `φ : L(H) ≃ G|K`, the paper's four objects are

* `P₁` — the `m-1` edges of the track `P`, in order (the paper's `R_{1,2}`);
* `P₂` — the `k-1` edges of the track `Q`, in order (the paper's `R_{3,4}`);
* `Q₁ = [u₁, u₄]`, `Q₂ = [u₂, u₃]` — the two antipaths of length 1.

Every clause of `IsKnot` is then a statement about which of these edges of `H` share an
endpoint: two vertices of `L(H)` are adjacent exactly when the corresponding edges of `H` are
distinct and meet, and `φ` carries that to `G`-adjacency because it is an isomorphism onto the
*induced* subgraph `G|K`.  Since `P` and `Q` are `Nodup` and vertex-disjoint, all of those
questions reduce to arithmetic on the indices; that reduction is what `key`/`keyeq` below do,
and `knot_of_index_data` then reads off the whole table.

Note the twist recorded in the paper's third bullet of the definition of a knot: the only
edges between `V(P₂)` and `{x₂, y₂}` are `a₂y₂` and `b₂x₂` — which is why the labelling here
takes `x₂ := u₂ = p₁q_k` and `y₂ := u₃ = p_mq₁` and not the other way round.

## Organisation

* `knot_of_index_data` — the combinatorial core.  It takes the appearance isomorphism and the
  two tracks presented as index functions `p, q : ℕ → W` (with `p 0 … p (M+1)` the vertices of
  the first track and `q 0 … q (L+1)` those of the second) and produces the knot.
* `exists_knot_of_degenerate_appearance` — the statement of the paper's sentence, obtained by
  feeding `exists_two_tracks_of_degenerate` into the core.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.KnotFromDegenerateAppearance

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.DegenerateK4Tracks

/-! ### Generic list plumbing

The two paths of the knot are the edge-lists of the two tracks, which we build as
`(List.range N).map f`.  These five lemmas are all we ever need about that shape. -/

section RangeMap

variable {A : Type*}

theorem length_rangeMap (N : ℕ) (f : ℕ → A) : ((List.range N).map f).length = N := by simp

theorem getElem_rangeMap {N : ℕ} (f : ℕ → A) (i : ℕ)
    (hi : i < ((List.range N).map f).length) : ((List.range N).map f)[i] = f i := by simp

theorem mem_rangeMap {N : ℕ} {f : ℕ → A} {a : A} :
    a ∈ (List.range N).map f ↔ ∃ i, i < N ∧ f i = a := by
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
    exact ⟨i, List.mem_range.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

theorem head?_rangeMap_succ (M : ℕ) (f : ℕ → A) :
    ((List.range (M + 1)).map f).head? = some (f 0) := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by simp)]
  simp

theorem getLast?_rangeMap_succ (M : ℕ) (f : ℕ → A) :
    ((List.range (M + 1)).map f).getLast? = some (f M) := by
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by simp)]
  simp

end RangeMap

/-! ### Two elementary facts -/

/-- Two edges of a graph, written as unordered pairs, meet exactly when one of the four
pairings of their endpoints coincides. -/
theorem sym2_meet_iff {W : Type*} (a b c d : W) :
    (∃ v, v ∈ s(a, b) ∧ v ∈ s(c, d)) ↔ (a = c ∨ a = d ∨ b = c ∨ b = d) := by
  simp only [Sym2.mem_iff]
  constructor
  · rintro ⟨v, (rfl | rfl), (h | h)⟩ <;> simp [h]
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨_, Or.inl rfl, Or.inl rfl⟩, ⟨_, Or.inl rfl, Or.inr rfl⟩,
            ⟨_, Or.inr rfl, Or.inl rfl⟩, ⟨_, Or.inr rfl, Or.inr rfl⟩]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A two-vertex list of adjacent distinct vertices is a path of length one. -/
theorem isPathFrom_pair {G : SimpleGraph V} {u v : V} (hne : u ≠ v) (hadj : G.Adj u v) :
    IsPathFrom G [u, v] u v := by
  refine ⟨⟨by simp, by simp [hne], ?_⟩, by simp, by simp⟩
  intro i j hi hj
  simp only [List.length_cons, List.length_nil] at hi hj
  have hi2 : i = 0 ∨ i = 1 := by omega
  have hj2 : j = 0 ∨ j = 1 := by omega
  rcases hi2 with rfl | rfl <;> rcases hj2 with rfl | rfl <;>
    simp [hadj, hadj.symm, hne, hne.symm, SimpleGraph.irrefl]

/-! ### The combinatorial core -/

/-- **The paper's construction, in index form.**

`p 0, …, p (M+1)` and `q 0, …, q (L+1)` are the vertices of the paper's two tracks
`p₁-⋯-p_m` and `q₁-⋯-q_k` (so `m = M + 2` and `k = L + 2`, and `M`, `L` odd is the paper's
`m`, `k` odd); `hpinj`, `hqinj`, `hpq` say that they are `Nodup` and vertex-disjoint; and
`c1 … c4` are the paper's four cross edges `p₁q₁`, `p₁q_k`, `p_mq₁`, `p_mq_k`.

The conclusion is the paper's knot, with `P₁, P₂` the edge-lists of the two tracks read into
`G` along the appearance isomorphism, and `Q₁, Q₂` the two length-one antipaths formed by the
four cross edges. -/
theorem knot_of_index_data {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) (M L : ℕ) (hM : 1 ≤ M) (hL : 1 ≤ L)
    (hMo : Odd M) (hLo : Odd L) (p q : ℕ → W)
    (hpadj : ∀ i, i ≤ M → H.Adj (p i) (p (i + 1)))
    (hqadj : ∀ j, j ≤ L → H.Adj (q j) (q (j + 1)))
    (hpinj : ∀ i j, i ≤ M + 1 → j ≤ M + 1 → p i = p j → i = j)
    (hqinj : ∀ i j, i ≤ L + 1 → j ≤ L + 1 → q i = q j → i = j)
    (hpq : ∀ i j, i ≤ M + 1 → j ≤ L + 1 → p i ≠ q j)
    (c1 : H.Adj (p 0) (q 0)) (c2 : H.Adj (p 0) (q (L + 1)))
    (c3 : H.Adj (p (M + 1)) (q 0)) (c4 : H.Adj (p (M + 1)) (q (L + 1))) :
    ∃ P₁ P₂ Q₁ Q₂ : List V,
      IsKnot G P₁ P₂ Q₁ Q₂ ∧
      pathLength Q₁ = 1 ∧ pathLength Q₂ = 1 ∧
      Odd (pathLength P₁) ∧ Odd (pathLength P₂) := by
  classical
  -- A total labelling of the edges of `H` by the corresponding vertices of `G`.
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : W → W → V, ∀ (a b : W) (h : H.Adj a b),
      Ψ a b = ((φ ⟨s(a, b), h⟩ : ↥K) : V) :=
    ⟨fun a b => if h : H.Adj a b then ((φ ⟨s(a, b), h⟩ : ↥K) : V)
      else ((φ ⟨s(p 0, q 0), c1⟩ : ↥K) : V), fun _ _ h => dif_pos h⟩
  -- Adjacency in `G` between two labels is "distinct edges of `H` that meet".
  have key : ∀ a b c d : W, H.Adj a b → H.Adj c d →
      (G.Adj (Ψ a b) (Ψ c d) ↔ (s(a, b) ≠ s(c, d) ∧ (a = c ∨ a = d ∨ b = c ∨ b = d))) := by
    intro a b c d hab hcd
    rw [hΨ a b hab, hΨ c d hcd]
    have h1 : G.Adj ((φ ⟨s(a, b), hab⟩ : ↥K) : V) ((φ ⟨s(c, d), hcd⟩ : ↥K) : V)
        ↔ H.lineGraph.Adj ⟨s(a, b), hab⟩ ⟨s(c, d), hcd⟩ := φ.map_adj_iff
    rw [h1, SimpleGraph.lineGraph_adj_iff_exists]
    constructor
    · rintro ⟨hne, v, hv1, hv2⟩
      exact ⟨fun h => hne (Subtype.ext h), (sym2_meet_iff a b c d).mp ⟨v, hv1, hv2⟩⟩
    · rintro ⟨hne, hm⟩
      obtain ⟨v, hv1, hv2⟩ := (sym2_meet_iff a b c d).mpr hm
      exact ⟨fun h => hne (congrArg Subtype.val h), v, hv1, hv2⟩
  -- Two labels are equal exactly when the two edges of `H` are.
  have keyeq : ∀ a b c d : W, H.Adj a b → H.Adj c d →
      (Ψ a b = Ψ c d ↔ s(a, b) = s(c, d)) := by
    intro a b c d hab hcd
    rw [hΨ a b hab, hΨ c d hcd]
    constructor
    · intro h
      exact congrArg Subtype.val (φ.injective (Subtype.ext h))
    · intro h
      exact congrArg (fun e => ((φ e : ↥K) : V))
        (Subtype.ext h : (⟨s(a, b), hab⟩ : H.edgeSet) = ⟨s(c, d), hcd⟩)
  have peq : ∀ i j, i ≤ M + 1 → j ≤ M + 1 → (p i = p j ↔ i = j) :=
    fun i j hi hj => ⟨hpinj i j hi hj, fun h => by rw [h]⟩
  have qeq : ∀ i j, i ≤ L + 1 → j ≤ L + 1 → (q i = q j ↔ i = j) :=
    fun i j hi hj => ⟨hqinj i j hi hj, fun h => by rw [h]⟩
  -- ### The meeting table, index by index.
  have adjPP : ∀ i j, i ≤ M → j ≤ M →
      (G.Adj (Ψ (p i) (p (i + 1))) (Ψ (p j) (p (j + 1))) ↔ (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hi hj
    rw [key _ _ _ _ (hpadj i hi) (hpadj j hj)]
    constructor
    · rintro ⟨hne, hm⟩
      rw [peq i j (by omega) (by omega), peq i (j + 1) (by omega) (by omega),
        peq (i + 1) j (by omega) (by omega),
        peq (i + 1) (j + 1) (by omega) (by omega)] at hm
      rcases hm with h | h | h | h
      · exfalso
        apply hne
        rw [h]
      · exact Or.inr h.symm
      · exact Or.inl h
      · exfalso
        apply hne
        have hij : i = j := by omega
        rw [hij]
    · intro h
      refine ⟨?_, ?_⟩
      · intro heq
        rw [Sym2.eq_iff, peq i j (by omega) (by omega),
          peq (i + 1) (j + 1) (by omega) (by omega),
          peq i (j + 1) (by omega) (by omega),
          peq (i + 1) j (by omega) (by omega)] at heq
        omega
      · rcases h with h | h
        · exact Or.inr (Or.inr (Or.inl (by rw [h])))
        · exact Or.inr (Or.inl (by rw [h]))
  have adjQQ : ∀ i j, i ≤ L → j ≤ L →
      (G.Adj (Ψ (q i) (q (i + 1))) (Ψ (q j) (q (j + 1))) ↔ (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hi hj
    rw [key _ _ _ _ (hqadj i hi) (hqadj j hj)]
    constructor
    · rintro ⟨hne, hm⟩
      rw [qeq i j (by omega) (by omega), qeq i (j + 1) (by omega) (by omega),
        qeq (i + 1) j (by omega) (by omega),
        qeq (i + 1) (j + 1) (by omega) (by omega)] at hm
      rcases hm with h | h | h | h
      · exfalso
        apply hne
        rw [h]
      · exact Or.inr h.symm
      · exact Or.inl h
      · exfalso
        apply hne
        have hij : i = j := by omega
        rw [hij]
    · intro h
      refine ⟨?_, ?_⟩
      · intro heq
        rw [Sym2.eq_iff, qeq i j (by omega) (by omega),
          qeq (i + 1) (j + 1) (by omega) (by omega),
          qeq i (j + 1) (by omega) (by omega),
          qeq (i + 1) j (by omega) (by omega)] at heq
        omega
      · rcases h with h | h
        · exact Or.inr (Or.inr (Or.inl (by rw [h])))
        · exact Or.inr (Or.inl (by rw [h]))
  have adjPQ : ∀ i j, i ≤ M → j ≤ L →
      ¬ G.Adj (Ψ (p i) (p (i + 1))) (Ψ (q j) (q (j + 1))) := by
    intro i j hi hj
    rw [key _ _ _ _ (hpadj i hi) (hqadj j hj)]
    rintro ⟨-, (h | h | h | h)⟩ <;> exact hpq _ _ (by omega) (by omega) h
  have adjPX : ∀ i s t, i ≤ M → s ≤ M + 1 → t ≤ L + 1 → H.Adj (p s) (q t) →
      (G.Adj (Ψ (p i) (p (i + 1))) (Ψ (p s) (q t)) ↔ (i = s ∨ i + 1 = s)) := by
    intro i s t hi hs ht hst
    rw [key _ _ _ _ (hpadj i hi) hst]
    constructor
    · rintro ⟨-, (h | h | h | h)⟩
      · exact Or.inl (hpinj _ _ (by omega) (by omega) h)
      · exact absurd h (hpq _ _ (by omega) (by omega))
      · exact Or.inr (hpinj _ _ (by omega) (by omega) h)
      · exact absurd h (hpq _ _ (by omega) (by omega))
    · intro h
      refine ⟨?_, ?_⟩
      · intro heq
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact hpq _ _ (by omega) (by omega) h2
        · exact hpq _ _ (by omega) (by omega) h1
      · rcases h with h | h
        · exact Or.inl (by rw [h])
        · exact Or.inr (Or.inr (Or.inl (by rw [h])))
  have adjQX : ∀ j s t, j ≤ L → s ≤ M + 1 → t ≤ L + 1 → H.Adj (p s) (q t) →
      (G.Adj (Ψ (q j) (q (j + 1))) (Ψ (p s) (q t)) ↔ (j = t ∨ j + 1 = t)) := by
    intro j s t hj hs ht hst
    rw [key _ _ _ _ (hqadj j hj) hst]
    constructor
    · rintro ⟨-, (h | h | h | h)⟩
      · exact absurd h.symm (hpq _ _ (by omega) (by omega))
      · exact Or.inl (hqinj _ _ (by omega) (by omega) h)
      · exact absurd h.symm (hpq _ _ (by omega) (by omega))
      · exact Or.inr (hqinj _ _ (by omega) (by omega) h)
    · intro h
      refine ⟨?_, ?_⟩
      · intro heq
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact hpq _ _ (by omega) (by omega) h1.symm
        · exact hpq _ _ (by omega) (by omega) h2.symm
      · rcases h with h | h
        · exact Or.inr (Or.inl (by rw [h]))
        · exact Or.inr (Or.inr (Or.inr (by rw [h])))
  have adjXX : ∀ s t s' t', s ≤ M + 1 → t ≤ L + 1 → s' ≤ M + 1 → t' ≤ L + 1 →
      H.Adj (p s) (q t) → H.Adj (p s') (q t') →
      (G.Adj (Ψ (p s) (q t)) (Ψ (p s') (q t')) ↔
        (¬ (s = s' ∧ t = t') ∧ (s = s' ∨ t = t'))) := by
    intro s t s' t' hs ht hs' ht' h1 h2
    rw [key _ _ _ _ h1 h2]
    constructor
    · rintro ⟨hne, hm⟩
      refine ⟨?_, ?_⟩
      · rintro ⟨rfl, rfl⟩
        exact hne rfl
      · rcases hm with h | h | h | h
        · exact Or.inl (hpinj _ _ (by omega) (by omega) h)
        · exact absurd h (hpq _ _ (by omega) (by omega))
        · exact absurd h.symm (hpq _ _ (by omega) (by omega))
        · exact Or.inr (hqinj _ _ (by omega) (by omega) h)
    · rintro ⟨hne, hm⟩
      refine ⟨?_, ?_⟩
      · intro heq
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨ha, hb⟩ | ⟨ha, -⟩
        · exact hne ⟨hpinj _ _ (by omega) (by omega) ha,
            hqinj _ _ (by omega) (by omega) hb⟩
        · exact hpq _ _ (by omega) (by omega) ha
      · rcases hm with h | h
        · exact Or.inl (by rw [h])
        · exact Or.inr (Or.inr (Or.inr (by rw [h])))
  -- ### The equality table.
  have eqPP : ∀ i j, i ≤ M → j ≤ M →
      (Ψ (p i) (p (i + 1)) = Ψ (p j) (p (j + 1)) ↔ i = j) := by
    intro i j hi hj
    rw [keyeq _ _ _ _ (hpadj i hi) (hpadj j hj), Sym2.eq_iff,
      peq i j (by omega) (by omega), peq (i + 1) (j + 1) (by omega) (by omega),
      peq i (j + 1) (by omega) (by omega), peq (i + 1) j (by omega) (by omega)]
    omega
  have eqQQ : ∀ i j, i ≤ L → j ≤ L →
      (Ψ (q i) (q (i + 1)) = Ψ (q j) (q (j + 1)) ↔ i = j) := by
    intro i j hi hj
    rw [keyeq _ _ _ _ (hqadj i hi) (hqadj j hj), Sym2.eq_iff,
      qeq i j (by omega) (by omega), qeq (i + 1) (j + 1) (by omega) (by omega),
      qeq i (j + 1) (by omega) (by omega), qeq (i + 1) j (by omega) (by omega)]
    omega
  have eqPQ : ∀ i j, i ≤ M → j ≤ L →
      Ψ (p i) (p (i + 1)) ≠ Ψ (q j) (q (j + 1)) := by
    intro i j hi hj h
    rw [keyeq _ _ _ _ (hpadj i hi) (hqadj j hj), Sym2.eq_iff] at h
    rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ <;> exact hpq _ _ (by omega) (by omega) h1
  have eqPX : ∀ i s t, i ≤ M → s ≤ M + 1 → t ≤ L + 1 → H.Adj (p s) (q t) →
      Ψ (p i) (p (i + 1)) ≠ Ψ (p s) (q t) := by
    intro i s t hi hs ht hst h
    rw [keyeq _ _ _ _ (hpadj i hi) hst, Sym2.eq_iff] at h
    rcases h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hpq _ _ (by omega) (by omega) h2
    · exact hpq _ _ (by omega) (by omega) h1
  have eqQX : ∀ j s t, j ≤ L → s ≤ M + 1 → t ≤ L + 1 → H.Adj (p s) (q t) →
      Ψ (q j) (q (j + 1)) ≠ Ψ (p s) (q t) := by
    intro j s t hj hs ht hst h
    rw [keyeq _ _ _ _ (hqadj j hj) hst, Sym2.eq_iff] at h
    rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hpq _ _ (by omega) (by omega) h1.symm
    · exact hpq _ _ (by omega) (by omega) h2.symm
  have eqXX : ∀ s t s' t', s ≤ M + 1 → t ≤ L + 1 → s' ≤ M + 1 → t' ≤ L + 1 →
      H.Adj (p s) (q t) → H.Adj (p s') (q t') →
      (Ψ (p s) (q t) = Ψ (p s') (q t') ↔ (s = s' ∧ t = t')) := by
    intro s t s' t' hs ht hs' ht' h1 h2
    rw [keyeq _ _ _ _ h1 h2, Sym2.eq_iff]
    constructor
    · rintro (⟨ha, hb⟩ | ⟨ha, -⟩)
      · exact ⟨hpinj _ _ (by omega) (by omega) ha, hqinj _ _ (by omega) (by omega) hb⟩
      · exact absurd ha (hpq _ _ (by omega) (by omega))
    · rintro ⟨rfl, rfl⟩
      exact Or.inl ⟨rfl, rfl⟩
  -- ### Opaque names for the vertices of `G` we are about to use.
  obtain ⟨gp, hgp⟩ : ∃ f : ℕ → V, ∀ i, f i = Ψ (p i) (p (i + 1)) := ⟨_, fun _ => rfl⟩
  obtain ⟨gq, hgq⟩ : ∃ f : ℕ → V, ∀ j, f j = Ψ (q j) (q (j + 1)) := ⟨_, fun _ => rfl⟩
  obtain ⟨x₁, hx₁⟩ : ∃ v : V, v = Ψ (p 0) (q 0) := ⟨_, rfl⟩
  obtain ⟨y₁, hy₁⟩ : ∃ v : V, v = Ψ (p (M + 1)) (q (L + 1)) := ⟨_, rfl⟩
  obtain ⟨x₂, hx₂⟩ : ∃ v : V, v = Ψ (p 0) (q (L + 1)) := ⟨_, rfl⟩
  obtain ⟨y₂, hy₂⟩ : ∃ v : V, v = Ψ (p (M + 1)) (q 0) := ⟨_, rfl⟩
  -- ### The table, restated in those names.
  have egp : ∀ i j, i ≤ M → j ≤ M → (gp i = gp j ↔ i = j) := by
    intro i j hi hj; rw [hgp, hgp]; exact eqPP i j hi hj
  have egq : ∀ i j, i ≤ L → j ≤ L → (gq i = gq j ↔ i = j) := by
    intro i j hi hj; rw [hgq, hgq]; exact eqQQ i j hi hj
  have engpq : ∀ i j, i ≤ M → j ≤ L → gp i ≠ gq j := by
    intro i j hi hj; rw [hgp, hgq]; exact eqPQ i j hi hj
  have engpx₁ : ∀ i, i ≤ M → gp i ≠ x₁ := by
    intro i hi; rw [hgp, hx₁]; exact eqPX i 0 0 hi (by omega) (by omega) c1
  have engpy₁ : ∀ i, i ≤ M → gp i ≠ y₁ := by
    intro i hi; rw [hgp, hy₁]; exact eqPX i (M + 1) (L + 1) hi (by omega) (by omega) c4
  have engpx₂ : ∀ i, i ≤ M → gp i ≠ x₂ := by
    intro i hi; rw [hgp, hx₂]; exact eqPX i 0 (L + 1) hi (by omega) (by omega) c2
  have engpy₂ : ∀ i, i ≤ M → gp i ≠ y₂ := by
    intro i hi; rw [hgp, hy₂]; exact eqPX i (M + 1) 0 hi (by omega) (by omega) c3
  have engqx₁ : ∀ j, j ≤ L → gq j ≠ x₁ := by
    intro j hj; rw [hgq, hx₁]; exact eqQX j 0 0 hj (by omega) (by omega) c1
  have engqy₁ : ∀ j, j ≤ L → gq j ≠ y₁ := by
    intro j hj; rw [hgq, hy₁]; exact eqQX j (M + 1) (L + 1) hj (by omega) (by omega) c4
  have engqx₂ : ∀ j, j ≤ L → gq j ≠ x₂ := by
    intro j hj; rw [hgq, hx₂]; exact eqQX j 0 (L + 1) hj (by omega) (by omega) c2
  have engqy₂ : ∀ j, j ≤ L → gq j ≠ y₂ := by
    intro j hj; rw [hgq, hy₂]; exact eqQX j (M + 1) 0 hj (by omega) (by omega) c3
  have hx1y1 : x₁ ≠ y₁ := by
    rw [hx₁, hy₁]
    intro h
    have := (eqXX 0 0 (M + 1) (L + 1) (by omega) (by omega) (by omega) (by omega) c1 c4).mp h
    omega
  have hx2y2 : x₂ ≠ y₂ := by
    rw [hx₂, hy₂]
    intro h
    have := (eqXX 0 (L + 1) (M + 1) 0 (by omega) (by omega) (by omega) (by omega) c2 c3).mp h
    omega
  have hx1x2 : x₁ ≠ x₂ := by
    rw [hx₁, hx₂]
    intro h
    have := (eqXX 0 0 0 (L + 1) (by omega) (by omega) (by omega) (by omega) c1 c2).mp h
    omega
  have hx1y2 : x₁ ≠ y₂ := by
    rw [hx₁, hy₂]
    intro h
    have := (eqXX 0 0 (M + 1) 0 (by omega) (by omega) (by omega) (by omega) c1 c3).mp h
    omega
  have hy1x2 : y₁ ≠ x₂ := by
    rw [hy₁, hx₂]
    intro h
    have := (eqXX (M + 1) (L + 1) 0 (L + 1)
      (by omega) (by omega) (by omega) (by omega) c4 c2).mp h
    omega
  have hy1y2 : y₁ ≠ y₂ := by
    rw [hy₁, hy₂]
    intro h
    have := (eqXX (M + 1) (L + 1) (M + 1) 0
      (by omega) (by omega) (by omega) (by omega) c4 c3).mp h
    omega
  have hab1 : gp 0 ≠ gp M := by
    intro h; have := (egp 0 M (by omega) (by omega)).mp h; omega
  have hab2 : gq 0 ≠ gq L := by
    intro h; have := (egq 0 L (by omega) (by omega)).mp h; omega
  -- adjacency along the two paths
  have apP : ∀ i j, i ≤ M → j ≤ M →
      (G.Adj (gp i) (gp j) ↔ (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hi hj; rw [hgp, hgp]; exact adjPP i j hi hj
  have aqQ : ∀ i j, i ≤ L → j ≤ L →
      (G.Adj (gq i) (gq j) ↔ (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hi hj; rw [hgq, hgq]; exact adjQQ i j hi hj
  have apq : ∀ i j, i ≤ M → j ≤ L → ¬ G.Adj (gp i) (gq j) := by
    intro i j hi hj; rw [hgp, hgq]; exact adjPQ i j hi hj
  -- adjacency between the paths and the four cross vertices
  have apx1 : ∀ i, i ≤ M → (G.Adj (gp i) x₁ ↔ i = 0) := by
    intro i hi
    rw [hgp, hx₁, adjPX i 0 0 hi (by omega) (by omega) c1]
    constructor
    · rintro (h | h) <;> omega
    · exact Or.inl
  have apy1 : ∀ i, i ≤ M → (G.Adj (gp i) y₁ ↔ i = M) := by
    intro i hi
    rw [hgp, hy₁, adjPX i (M + 1) (L + 1) hi (by omega) (by omega) c4]
    constructor
    · rintro (h | h) <;> omega
    · intro h; exact Or.inr (by omega)
  have apx2 : ∀ i, i ≤ M → (G.Adj (gp i) x₂ ↔ i = 0) := by
    intro i hi
    rw [hgp, hx₂, adjPX i 0 (L + 1) hi (by omega) (by omega) c2]
    constructor
    · rintro (h | h) <;> omega
    · exact Or.inl
  have apy2 : ∀ i, i ≤ M → (G.Adj (gp i) y₂ ↔ i = M) := by
    intro i hi
    rw [hgp, hy₂, adjPX i (M + 1) 0 hi (by omega) (by omega) c3]
    constructor
    · rintro (h | h) <;> omega
    · intro h; exact Or.inr (by omega)
  have aqx1 : ∀ j, j ≤ L → (G.Adj (gq j) x₁ ↔ j = 0) := by
    intro j hj
    rw [hgq, hx₁, adjQX j 0 0 hj (by omega) (by omega) c1]
    constructor
    · rintro (h | h) <;> omega
    · exact Or.inl
  have aqy1 : ∀ j, j ≤ L → (G.Adj (gq j) y₁ ↔ j = L) := by
    intro j hj
    rw [hgq, hy₁, adjQX j (M + 1) (L + 1) hj (by omega) (by omega) c4]
    constructor
    · rintro (h | h) <;> omega
    · intro h; exact Or.inr (by omega)
  have aqx2 : ∀ j, j ≤ L → (G.Adj (gq j) x₂ ↔ j = L) := by
    intro j hj
    rw [hgq, hx₂, adjQX j 0 (L + 1) hj (by omega) (by omega) c2]
    constructor
    · rintro (h | h) <;> omega
    · intro h; exact Or.inr (by omega)
  have aqy2 : ∀ j, j ≤ L → (G.Adj (gq j) y₂ ↔ j = 0) := by
    intro j hj
    rw [hgq, hy₂, adjQX j (M + 1) 0 hj (by omega) (by omega) c3]
    constructor
    · rintro (h | h) <;> omega
    · exact Or.inl
  -- symmetric forms, for the "nonedge" clauses of `IsKnot`
  have apx1' : ∀ i, i ≤ M → (G.Adj x₁ (gp i) ↔ i = 0) := by
    intro i hi; rw [SimpleGraph.adj_comm]; exact apx1 i hi
  have apy1' : ∀ i, i ≤ M → (G.Adj y₁ (gp i) ↔ i = M) := by
    intro i hi; rw [SimpleGraph.adj_comm]; exact apy1 i hi
  have apx2' : ∀ i, i ≤ M → (G.Adj x₂ (gp i) ↔ i = 0) := by
    intro i hi; rw [SimpleGraph.adj_comm]; exact apx2 i hi
  have apy2' : ∀ i, i ≤ M → (G.Adj y₂ (gp i) ↔ i = M) := by
    intro i hi; rw [SimpleGraph.adj_comm]; exact apy2 i hi
  have aqx1' : ∀ j, j ≤ L → (G.Adj x₁ (gq j) ↔ j = 0) := by
    intro j hj; rw [SimpleGraph.adj_comm]; exact aqx1 j hj
  have aqy1' : ∀ j, j ≤ L → (G.Adj y₁ (gq j) ↔ j = L) := by
    intro j hj; rw [SimpleGraph.adj_comm]; exact aqy1 j hj
  have aqx2' : ∀ j, j ≤ L → (G.Adj x₂ (gq j) ↔ j = L) := by
    intro j hj; rw [SimpleGraph.adj_comm]; exact aqx2 j hj
  have aqy2' : ∀ j, j ≤ L → (G.Adj y₂ (gq j) ↔ j = 0) := by
    intro j hj; rw [SimpleGraph.adj_comm]; exact aqy2 j hj
  -- adjacency among the four cross vertices
  have ax1x2 : G.Adj x₁ x₂ := by
    rw [hx₁, hx₂, adjXX 0 0 0 (L + 1) (by omega) (by omega) (by omega) (by omega) c1 c2]
    exact ⟨by omega, by omega⟩
  have ax1y2 : G.Adj x₁ y₂ := by
    rw [hx₁, hy₂, adjXX 0 0 (M + 1) 0 (by omega) (by omega) (by omega) (by omega) c1 c3]
    exact ⟨by omega, by omega⟩
  have ay1x2 : G.Adj y₁ x₂ := by
    rw [hy₁, hx₂,
      adjXX (M + 1) (L + 1) 0 (L + 1) (by omega) (by omega) (by omega) (by omega) c4 c2]
    exact ⟨by omega, by omega⟩
  have ay1y2 : G.Adj y₁ y₂ := by
    rw [hy₁, hy₂,
      adjXX (M + 1) (L + 1) (M + 1) 0 (by omega) (by omega) (by omega) (by omega) c4 c3]
    exact ⟨by omega, by omega⟩
  have nx1y1 : ¬ G.Adj x₁ y₁ := by
    rw [hx₁, hy₁,
      adjXX 0 0 (M + 1) (L + 1) (by omega) (by omega) (by omega) (by omega) c1 c4]
    rintro ⟨-, (h | h)⟩ <;> omega
  have nx2y2 : ¬ G.Adj x₂ y₂ := by
    rw [hx₂, hy₂,
      adjXX 0 (L + 1) (M + 1) 0 (by omega) (by omega) (by omega) (by omega) c2 c3]
    rintro ⟨-, (h | h)⟩ <;> omega
  -- ### Membership in the two paths.
  have hmemP₁ : ∀ v : V, v ∈ (List.range (M + 1)).map gp ↔ ∃ i, i ≤ M ∧ gp i = v := by
    intro v
    rw [mem_rangeMap]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, hi, rfl⟩; exact ⟨i, by omega, rfl⟩
  have hmemP₂ : ∀ v : V, v ∈ (List.range (L + 1)).map gq ↔ ∃ j, j ≤ L ∧ gq j = v := by
    intro v
    rw [mem_rangeMap]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨j, by omega, rfl⟩
    · rintro ⟨j, hj, rfl⟩; exact ⟨j, by omega, rfl⟩
  -- ### The two paths of the knot are induced paths.
  have hpath₁ : IsPathFrom G ((List.range (M + 1)).map gp) (gp 0) (gp M) := by
    refine ⟨⟨by simp, ?_, ?_⟩, head?_rangeMap_succ M gp, getLast?_rangeMap_succ M gp⟩
    · refine List.Nodup.map_on ?_ List.nodup_range
      intro a ha b hb hab
      rw [List.mem_range] at ha hb
      exact (egp a b (by omega) (by omega)).mp hab
    · intro i j hi hj
      have hi' : i ≤ M := by have h := hi; rw [length_rangeMap] at h; omega
      have hj' : j ≤ M := by have h := hj; rw [length_rangeMap] at h; omega
      rw [getElem_rangeMap gp i hi, getElem_rangeMap gp j hj]
      exact apP i j hi' hj'
  have hpath₂ : IsPathFrom G ((List.range (L + 1)).map gq) (gq 0) (gq L) := by
    refine ⟨⟨by simp, ?_, ?_⟩, head?_rangeMap_succ L gq, getLast?_rangeMap_succ L gq⟩
    · refine List.Nodup.map_on ?_ List.nodup_range
      intro a ha b hb hab
      rw [List.mem_range] at ha hb
      exact (egq a b (by omega) (by omega)).mp hab
    · intro i j hi hj
      have hi' : i ≤ L := by have h := hi; rw [length_rangeMap] at h; omega
      have hj' : j ≤ L := by have h := hj; rw [length_rangeMap] at h; omega
      rw [getElem_rangeMap gq i hi, getElem_rangeMap gq j hj]
      exact aqQ i j hi' hj'
  -- ### Assemble.
  refine ⟨(List.range (M + 1)).map gp, (List.range (L + 1)).map gq, [x₁, y₁], [x₂, y₂],
    ?_, by simp [pathLength], by simp [pathLength], ?_, ?_⟩
  · refine ⟨gp 0, gp M, gq 0, gq L, x₁, y₁, x₂, y₂, hpath₁, hpath₂, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (3) `Q₁` is an antipath of length one
      exact isPathFrom_pair hx1y1 ((SimpleGraph.compl_adj G _ _).mpr ⟨hx1y1, nx1y1⟩)
    · -- (4) `Q₂` is an antipath of length one
      exact isPathFrom_pair hx2y2 ((SimpleGraph.compl_adj G _ _).mpr ⟨hx2y2, nx2y2⟩)
    · -- (5) `V(P₁) ∩ V(P₂) = ∅`
      intro v hv hv2
      obtain ⟨i, hi, rfl⟩ := (hmemP₁ v).mp hv
      obtain ⟨j, hj, hj2⟩ := (hmemP₂ _).mp hv2
      exact engpq i j hi hj hj2.symm
    · -- (6) `V(P₁) ∩ V(Q₁) = ∅`
      intro v hv hv2
      obtain ⟨i, hi, rfl⟩ := (hmemP₁ v).mp hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv2
      rcases hv2 with h | h
      · exact engpx₁ i hi h
      · exact engpy₁ i hi h
    · -- (7) `V(P₁) ∩ V(Q₂) = ∅`
      intro v hv hv2
      obtain ⟨i, hi, rfl⟩ := (hmemP₁ v).mp hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv2
      rcases hv2 with h | h
      · exact engpx₂ i hi h
      · exact engpy₂ i hi h
    · -- (8) `V(P₂) ∩ V(Q₁) = ∅`
      intro v hv hv2
      obtain ⟨j, hj, rfl⟩ := (hmemP₂ v).mp hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv2
      rcases hv2 with h | h
      · exact engqx₁ j hj h
      · exact engqy₁ j hj h
    · -- (9) `V(P₂) ∩ V(Q₂) = ∅`
      intro v hv hv2
      obtain ⟨j, hj, rfl⟩ := (hmemP₂ v).mp hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv2
      rcases hv2 with h | h
      · exact engqx₂ j hj h
      · exact engqy₂ j hj h
    · -- (10) `V(Q₁) ∩ V(Q₂) = ∅`
      intro v hv hv2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv hv2
      rcases hv with rfl | rfl <;> rcases hv2 with h | h
      · exact hx1x2 h
      · exact hx1y2 h
      · exact hy1x2 h
      · exact hy1y2 h
    · -- (11) `P₁` has length ≥ 1
      simp only [pathLength, length_rangeMap]
      omega
    · -- (12) `P₂` has length ≥ 1
      simp only [pathLength, length_rangeMap]
      omega
    · -- (13) `Q₁` has length ≥ 1
      simp [pathLength]
    · -- (14) `Q₂` has length ≥ 1
      simp [pathLength]
    · -- (15) there are no edges between `P₁` and `P₂`
      intro u hu w hw
      obtain ⟨i, hi, rfl⟩ := (hmemP₁ u).mp hu
      obtain ⟨j, hj, rfl⟩ := (hmemP₂ w).mp hw
      exact apq i j hi hj
    · -- (16) `Q₁` is complete to `Q₂`
      intro u hu w hw
      simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hu hw
      rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
      · exact ax1x2
      · exact ax1y2
      · exact ay1x2
      · exact ay1y2
    · -- (17) the only edges between `V(P₁)` and `{x₁, y₁}` are `a₁x₁` and `b₁y₁`
      intro u hu w hw
      obtain ⟨i, hi, rfl⟩ := (hmemP₁ u).mp hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · rw [apx1 i hi, egp i 0 hi (by omega), egp i M hi (by omega)]
        constructor
        · intro h; exact Or.inl ⟨h, rfl⟩
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact h
          · exact absurd h hx1y1
      · rw [apy1 i hi, egp i 0 hi (by omega), egp i M hi (by omega)]
        constructor
        · intro h; exact Or.inr ⟨h, rfl⟩
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact absurd h (Ne.symm hx1y1)
          · exact h
    · -- (18) the only edges between `V(P₁)` and `{x₂, y₂}` are `a₁x₂` and `b₁y₂`
      intro u hu w hw
      obtain ⟨i, hi, rfl⟩ := (hmemP₁ u).mp hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · rw [apx2 i hi, egp i 0 hi (by omega), egp i M hi (by omega)]
        constructor
        · intro h; exact Or.inl ⟨h, rfl⟩
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact h
          · exact absurd h hx2y2
      · rw [apy2 i hi, egp i 0 hi (by omega), egp i M hi (by omega)]
        constructor
        · intro h; exact Or.inr ⟨h, rfl⟩
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact absurd h (Ne.symm hx2y2)
          · exact h
    · -- (19) the only edges between `V(P₂)` and `{x₁, y₁}` are `a₂x₁` and `b₂y₁`
      intro u hu w hw
      obtain ⟨j, hj, rfl⟩ := (hmemP₂ u).mp hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · rw [aqx1 j hj, egq j 0 hj (by omega), egq j L hj (by omega)]
        constructor
        · intro h; exact Or.inl ⟨h, rfl⟩
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact h
          · exact absurd h hx1y1
      · rw [aqy1 j hj, egq j 0 hj (by omega), egq j L hj (by omega)]
        constructor
        · intro h; exact Or.inr ⟨h, rfl⟩
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact absurd h (Ne.symm hx1y1)
          · exact h
    · -- (20) the only edges between `V(P₂)` and `{x₂, y₂}` are `a₂y₂` and `b₂x₂`
      intro u hu w hw
      obtain ⟨j, hj, rfl⟩ := (hmemP₂ u).mp hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · rw [aqx2 j hj, egq j 0 hj (by omega), egq j L hj (by omega)]
        constructor
        · intro h; exact Or.inr ⟨h, rfl⟩
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact absurd h hx2y2
          · exact h
      · rw [aqy2 j hj, egq j 0 hj (by omega), egq j L hj (by omega)]
        constructor
        · intro h; exact Or.inl ⟨h, rfl⟩
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact h
          · exact absurd h (Ne.symm hx2y2)
    · -- (21) the only nonedges between `V(Q₁)` and `{a₁, b₁}` are `a₁y₁` and `b₁x₁`
      intro u hu w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
      · rw [apx1' 0 (by omega)]
        constructor
        · intro h; exact absurd rfl h
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact absurd h hx1y1
          · exact absurd h hab1
      · rw [apx1' M (by omega)]
        constructor
        · intro _; exact Or.inr ⟨rfl, rfl⟩
        · intro _; omega
      · rw [apy1' 0 (by omega)]
        constructor
        · intro _; exact Or.inl ⟨rfl, rfl⟩
        · intro _; omega
      · rw [apy1' M (by omega)]
        constructor
        · intro h; exact absurd rfl h
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact absurd h (Ne.symm hab1)
          · exact absurd h (Ne.symm hx1y1)
    · -- (22) the only nonedges between `V(Q₂)` and `{a₁, b₁}` are `a₁y₂` and `b₁x₂`
      intro u hu w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
      · rw [apx2' 0 (by omega)]
        constructor
        · intro h; exact absurd rfl h
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact absurd h hx2y2
          · exact absurd h hab1
      · rw [apx2' M (by omega)]
        constructor
        · intro _; exact Or.inr ⟨rfl, rfl⟩
        · intro _; omega
      · rw [apy2' 0 (by omega)]
        constructor
        · intro _; exact Or.inl ⟨rfl, rfl⟩
        · intro _; omega
      · rw [apy2' M (by omega)]
        constructor
        · intro h; exact absurd rfl h
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact absurd h (Ne.symm hab1)
          · exact absurd h (Ne.symm hx2y2)
    · -- (23) the only nonedges between `V(Q₁)` and `{a₂, b₂}` are `a₂y₁` and `b₂x₁`
      intro u hu w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
      · rw [aqx1' 0 (by omega)]
        constructor
        · intro h; exact absurd rfl h
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact absurd h hx1y1
          · exact absurd h hab2
      · rw [aqx1' L (by omega)]
        constructor
        · intro _; exact Or.inr ⟨rfl, rfl⟩
        · intro _; omega
      · rw [aqy1' 0 (by omega)]
        constructor
        · intro _; exact Or.inl ⟨rfl, rfl⟩
        · intro _; omega
      · rw [aqy1' L (by omega)]
        constructor
        · intro h; exact absurd rfl h
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact absurd h (Ne.symm hab2)
          · exact absurd h (Ne.symm hx1y1)
    · -- (24) the only nonedges between `V(Q₂)` and `{a₂, b₂}` are `a₂x₂` and `b₂y₂`
      intro u hu w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
      · rw [aqx2' 0 (by omega)]
        constructor
        · intro _; exact Or.inl ⟨rfl, rfl⟩
        · intro _; omega
      · rw [aqx2' L (by omega)]
        constructor
        · intro h; exact absurd rfl h
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact absurd h (Ne.symm hab2)
          · exact absurd h hx2y2
      · rw [aqy2' 0 (by omega)]
        constructor
        · intro h; exact absurd rfl h
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact absurd h (Ne.symm hx2y2)
          · exact absurd h hab2
      · rw [aqy2' L (by omega)]
        constructor
        · intro _; exact Or.inr ⟨rfl, rfl⟩
        · intro _; omega
  · -- `P₁` has odd length
    simpa only [pathLength, length_rangeMap, Nat.add_sub_cancel] using hMo
  · -- `P₂` has odd length
    simpa only [pathLength, length_rangeMap, Nat.add_sub_cancel] using hLo

/-! ### The statement of the paper's sentence -/

/-- **§9 preamble, printed p. 47.**

PAPER: *"If `L(H)` is a degenerate appearance of `K₄` in `G`, it can be viewed as a knot.  For,
in our usual notation, let `R_{1,3}, R_{1,4}, R_{2,3}, R_{2,4}` have length 0; let
`P₁ = R_{1,2}`, `P₂ = R_{3,4}`, let `Q₁` be the antipath `r_{1,3}-r_{2,4}`, and `Q₂` the
antipath `r_{1,4}-r_{2,3}`.  It is easy to check that this is a knot."*

The two antipaths have length 1 (the paper's `R_{i,j}` of length 0 are single vertices of
`L(H)`, and two of them span an antipath of length 1), and the two paths have odd length,
which is what the construction of a striation out of the knot needs. -/
theorem exists_knot_of_degenerate_appearance (G : SimpleGraph V)
    {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
    (happ : IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K)
    (hdeg : DegenerateK4Appearance H) :
    ∃ P₁ P₂ Q₁ Q₂ : List V,
      IsKnot G P₁ P₂ Q₁ Q₂ ∧
      pathLength Q₁ = 1 ∧ pathLength Q₂ = 1 ∧
      Odd (pathLength P₁) ∧ Odd (pathLength P₂) := by
  obtain ⟨⟨hsub, hbip⟩, ⟨φ⟩⟩ := happ
  obtain ⟨P, Q, hP3, hQ3, htP, htQ, hdisj, hoP, hoQ, e1, e2, e3, e4⟩ :=
    exists_two_tracks_of_degenerate hbip hsub hdeg
  have hP0 : 0 < P.length := by omega
  obtain ⟨pf, hpf⟩ : ∃ f : ℕ → Fin n, ∀ i, f i = P.getD i (P[0]'hP0) := ⟨_, fun _ => rfl⟩
  obtain ⟨qf, hqf⟩ : ∃ f : ℕ → Fin n, ∀ j, f j = Q.getD j (P[0]'hP0) := ⟨_, fun _ => rfl⟩
  have hpfv : ∀ (i : ℕ) (h : i < P.length), pf i = P[i] := by
    intro i h; rw [hpf]; exact List.getD_eq_getElem P _ h
  have hqfv : ∀ (j : ℕ) (h : j < Q.length), qf j = Q[j] := by
    intro j h; rw [hqf]; exact List.getD_eq_getElem Q _ h
  have hMe : P.length - 2 + 1 = P.length - 1 := by omega
  have hLe : Q.length - 2 + 1 = Q.length - 1 := by omega
  refine knot_of_index_data φ (P.length - 2) (Q.length - 2) (by omega) (by omega)
    ?_ ?_ pf qf ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Nat.odd_iff] at hoP ⊢; omega
  · rw [Nat.odd_iff] at hoQ ⊢; omega
  · intro i hi
    rw [hpfv i (by omega), hpfv (i + 1) (by omega)]
    exact htP.2.2 i (by omega)
  · intro j hj
    rw [hqfv j (by omega), hqfv (j + 1) (by omega)]
    exact htQ.2.2 j (by omega)
  · intro i j hi hj h
    rw [hpfv i (by omega), hpfv j (by omega)] at h
    exact (List.Nodup.getElem_inj_iff htP.2.1).mp h
  · intro i j hi hj h
    rw [hqfv i (by omega), hqfv j (by omega)] at h
    exact (List.Nodup.getElem_inj_iff htQ.2.1).mp h
  · intro i j hi hj h
    rw [hpfv i (by omega), hqfv j (by omega)] at h
    refine hdisj P[i] (by apply List.getElem_mem) ?_
    rw [h]
    apply List.getElem_mem
  · rw [hpfv 0 (by omega), hqfv 0 (by omega)]
    exact e1
  · rw [hLe, hpfv 0 (by omega), hqfv (Q.length - 1) (by omega)]
    exact e2
  · rw [hMe, hpfv (P.length - 1) (by omega), hqfv 0 (by omega)]
    exact e3
  · rw [hMe, hLe, hpfv (P.length - 1) (by omega), hqfv (Q.length - 1) (by omega)]
    exact e4

end Workspace.ProofLemmas.KnotFromDegenerateAppearance
