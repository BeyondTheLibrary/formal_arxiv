import Mathlib
import Workspace.Types.Core
import Workspace.Types.Knots
import Workspace.ProofLemmas.PathBasics

/-!
# A knot is a striation with `m = n = 2`

This module supplies the second half of the uncited sentence in the proof of 9.6
(printed p. 55):

> *"By hypothesis it is degenerate, and hence **there is a striation in `G`**; choose a maximal
> striation `L`."*

The paper gives no citation.  The passage is: a degenerate `K₄`-appearance *is* a knot (§9
preamble, printed p. 47: *"If `L(H)` is a degenerate appearance of `K₄` in `G`, it can be viewed
as a knot"*), and a knot *is* a striation with `m = n = 2` — the degenerate case of *"9.3
suggests that we should attempt to combine paths into strips … and combine antipaths into
'antistrips'.  Let us make that precise."* (printed p. 49).  This module supplies
**knot ⟹ striation**; the passage appearance ⟹ knot is elsewhere, and *"choose a maximal
striation"* is `Workspace.ProofLemmas.MaximalStriationExists.exists_maximalStriation`.

## The construction

From `IsKnot G P₁ P₂ Q₁ Q₂` with ends `a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂`, take `m = n = 2` and

```
S = ![ ({a₁}, P₁*, {b₁}), ({a₂}, P₂*, {b₂}) ]
T = ![ ({x₁}, ∅,  {y₁}), ({x₂}, ∅,  {y₂}) ]
```

Each `Pᵢ` is a rung of its own strip and each `Qⱼ` an antirung of its own antistrip, which is
what discharges the covering clause of `IsStrip`.  The antistrips' middle sets are empty
because `pathLength Qⱼ = 1` forces `Qⱼ` to have no interior.

## The two clauses that carry the content

* **Odd rungs.**  An antirung of `({xⱼ}, ∅, {yⱼ})` has empty interior, hence at most two
  vertices; its ends are `xⱼ ≠ yⱼ`, so it has exactly two, and length `1`.  A rung of
  `({aᵢ}, Pᵢ*, {bᵢ})` need **not** equal `Pᵢ`, so its parity is obtained by a 2-colouring
  instead: since `Pᵢ` is an *induced* path, `G`-adjacent vertices of `Pᵢ` sit at indices
  differing by one, hence of opposite parity, so index parity alternates along any rung
  (`rung_index_parity`, the path analogue of
  `Workspace.ProofLemmas.DegenerateK4Tracks.track_color`).  Reading it off at the far end gives
  `pathLength p ≡ pathLength Pᵢ (mod 2)`, which is odd by hypothesis.

* **The twist.**  Three of the four strip/antistrip pairs are parallel, read straight off the
  knot's clause *"the only edges between `V(Pᵢ)` and `{xⱼ, yⱼ}` are `aᵢxⱼ` and `bᵢyⱼ`"*.  The
  fourth pair is **co-parallel**, because the corresponding knot clause is the reversed pattern
  *"the only edges between `V(P₂)` and `{x₂, y₂}` are `a₂y₂` and `b₂x₂`"* — i.e. `S₂` is
  parallel to the reverse of `T₂`.  So `S₁, S₂` agree on `T₁` and disagree on `T₂`, which is
  exactly a twist, and the single quadruple `(S₁, S₂, T₁, T₂)` witnesses both twist clauses.

The knot's four *nonedge* clauses (those between `V(Qⱼ)` and `{aᵢ, bᵢ}`) are not needed: they
constrain the interiors of the `Qⱼ`, which are empty here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.StriationFromKnot

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.PathBasics

variable {V : Type*}

/-! ### `Fin 2` enumeration -/

private theorem fin_two_cases : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide

private theorem fin_two_lt : ∀ i i' : Fin 2, i < i' → i = 0 ∧ i' = 1 := by decide

private theorem fin_two_ne :
    ∀ i i' : Fin 2, i ≠ i' → (i = 0 ∧ i' = 1) ∨ (i = 1 ∧ i' = 0) := by decide

/-! ### Ends of a path are not repeated -/

private theorem notMem_tail_head {p : List V} {a : V} (hnd : p.Nodup)
    (ha : p.head? = some a) : a ∉ p.tail := by
  cases p with
  | nil => simp at ha
  | cons c t =>
      simp only [List.head?_cons, Option.some.injEq] at ha
      subst ha
      simp only [List.tail_cons]
      exact (List.nodup_cons.mp hnd).1

private theorem notMem_dropLast_getLast {p : List V} {b : V} (hnd : p.Nodup)
    (hb : p.getLast? = some b) : b ∉ p.dropLast := by
  have hne : p ≠ [] := by rintro rfl; simp at hb
  have hbe : b = p.getLast hne := by
    rw [List.getLast?_eq_some_getLast hne] at hb
    exact (Option.some_injective _ hb).symm
  intro hmem
  rw [mem_dropLast_iff hnd hne] at hmem
  exact hmem.2 hbe

/-! ### The strip spanned by a path

For a path `a-P-b`, the triple `({a}, P*, {b})` is a strip, `P` itself is one of its rungs, and
its vertex set `V(S) = {a} ∪ {b} ∪ P*` is the whole of `V(P)`.  The middle set is passed as a
parameter `C` together with an equation, so that the same three lemmas serve the antistrips,
whose middle set is written `∅`. -/

/-- A path is a rung of the strip it spans. -/
private theorem isSRung_self {G : SimpleGraph V} {p : List V} {a b : V} {C : Set V}
    (hp : IsPathFrom G p a b) (hC : C = {v : V | v ∈ SPGT.interior p}) :
    IsSRung G (({a} : Set V), C, ({b} : Set V)) p := by
  subst hC
  refine ⟨a, b, hp, rfl, rfl, ?_, ?_, fun v hv => hv⟩
  · intro v hv hva
    simp only [Set.mem_singleton_iff] at hva
    subst hva
    exact notMem_tail_head (path_nodup hp.1) hp.2.1 hv
  · intro v hv hvb
    simp only [Set.mem_singleton_iff] at hvb
    subst hvb
    exact notMem_dropLast_getLast (path_nodup hp.1) hp.2.2 hv

/-- `V(S) = {a} ∪ {b} ∪ P*` is the whole vertex set of the path. -/
private theorem stripVertices_pathTriple {G : SimpleGraph V} {p : List V} {a b : V} {C : Set V}
    (hp : IsPathFrom G p a b) (hC : C = {v : V | v ∈ SPGT.interior p}) :
    stripVertices (({a} : Set V), C, ({b} : Set V)) = {v : V | v ∈ p} := by
  subst hC
  ext z
  simp only [stripVertices, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro ((rfl | rfl) | hz)
    · exact head_mem hp.2.1
    · exact getLast_mem hp.2.2
    · exact interior_subset hz
  · intro hz
    by_cases hza : z = a
    · exact Or.inl (Or.inl hza)
    · by_cases hzb : z = b
      · exact Or.inl (Or.inr hzb)
      · exact Or.inr ((mem_interior_iff_of_pathFrom hp).mpr ⟨hz, hza, hzb⟩)

/-- The triple `({a}, P*, {b})` spanned by a path `a-P-b` of length `≥ 1` is a strip. -/
private theorem isStrip_of_pathFrom {G : SimpleGraph V} {p : List V} {a b : V} {C : Set V}
    (hp : IsPathFrom G p a b) (hab : a ≠ b) (hC : C = {v : V | v ∈ SPGT.interior p}) :
    IsStrip G (({a} : Set V), C, ({b} : Set V)) := by
  subst hC
  refine ⟨?_, ?_, ?_, ⟨a, rfl⟩, ⟨b, rfl⟩, ?_⟩
  · rw [Set.disjoint_singleton_left]
    simpa using hab
  · rw [Set.disjoint_singleton_left]
    intro hcon
    exact ((mem_interior_iff_of_pathFrom hp).mp hcon).2.1 rfl
  · rw [Set.disjoint_singleton_left]
    intro hcon
    exact ((mem_interior_iff_of_pathFrom hp).mp hcon).2.2 rfl
  · intro z hz
    refine ⟨p, isSRung_self hp rfl, ?_⟩
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hz
    rcases hz with (rfl | rfl) | hz
    · exact head_mem hp.2.1
    · exact getLast_mem hp.2.2
    · exact interior_subset hz

/-! ### A path of length one has empty interior -/

private theorem interior_eq_empty_of_length_one {q : List V} (hq : pathLength q = 1) :
    {v : V | v ∈ SPGT.interior q} = (∅ : Set V) := by
  have hlen : (SPGT.interior q).length = 0 := by
    have h := interior_length q
    rw [pathLength_eq] at hq
    omega
  have hnil : SPGT.interior q = [] := by
    rcases hi : SPGT.interior q with _ | ⟨c, t⟩
    · rfl
    · rw [hi] at hlen; simp at hlen
  ext z
  simp [hnil]

/-! ### Every antirung of `({x}, ∅, {y})` has length one

An `IsSRung` of a triple with empty middle set has empty interior, so at most two vertices; its
ends are `x` and `y`, which are distinct, so it has exactly two and length `1`, which is odd. -/

private theorem antirung_odd {G : SimpleGraph V} {p : List V} {x y : V} (hxy : x ≠ y)
    (hr : IsSRung G (({x} : Set V), (∅ : Set V), ({y} : Set V)) p) :
    Odd (pathLength p) := by
  obtain ⟨a', b', hpab, ha', hb', -, -, hint⟩ := hr
  simp only [Set.mem_singleton_iff] at ha' hb'
  rw [ha', hb'] at hpab
  have hnil : SPGT.interior p = [] := by
    rcases hi : SPGT.interior p with _ | ⟨c, t⟩
    · rfl
    · exact absurd (hint c (by rw [hi]; simp)) (by simp)
  have hlen2 : p.length ≤ 2 := by
    have h := interior_length p
    rw [hnil] at h
    simp only [List.length_nil] at h
    omega
  have hpos : 0 < p.length := path_length_pos hpab.1
  have hlen : p.length = 2 := by
    rcases Nat.eq_or_lt_of_le hpos with h | h
    · exfalso
      have h1 : p.length = 1 := h.symm
      obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp h1
      have hx' : c = x := by have := hpab.2.1; simp at this; exact this
      have hy' : c = y := by have := hpab.2.2; simp at this; exact this
      exact hxy (hx'.symm.trans hy')
    · omega
  rw [pathLength_eq, hlen]
  exact odd_one

/-! ### Parity along a rung: the alternation argument -/

/-- **Index parity transfers from `P` to any rung of the strip `P` spans.**

This is the 2-colouring of `Workspace.ProofLemmas.DegenerateK4Tracks.track_color` transported
from tracks to paths.  `IsPathList` states adjacency as `G.Adj P[i] P[j] ↔ i + 1 = j ∨ j + 1 = i`
— the path is *induced* — so two `G`-adjacent vertices of `P` sit at indices of opposite parity.
Walking along `p`, whose vertices all lie on `P` and whose consecutive vertices are `G`-adjacent,
the index parity therefore flips at every step: `col p[t] ≡ col p[0] + t (mod 2)`. -/
private theorem rung_index_parity {G : SimpleGraph V} {P p : List V} {a : V}
    (hP : IsPathList G P) (hPa : P.head? = some a)
    (hp : IsPathList G p) (hpa : p.head? = some a)
    (hsub : ∀ v ∈ p, v ∈ P) :
    ∀ (t : ℕ) (ht : t < p.length),
      ∃ (k : ℕ) (hk : k < P.length), P[k]'hk = p[t]'ht ∧ k % 2 = t % 2 := by
  intro t
  induction t with
  | zero =>
      intro ht
      have hP0 : 0 < P.length := path_length_pos hP
      refine ⟨0, hP0, ?_, rfl⟩
      rw [getElem_zero_of_head? hPa hP0, getElem_zero_of_head? hpa ht]
  | succ s ih =>
      intro ht
      have hs : s < p.length := by omega
      obtain ⟨k, hk, hkeq, hpar⟩ := ih hs
      have hmem : p[s + 1]'ht ∈ P := hsub _ (List.getElem_mem ht)
      obtain ⟨k', hk', hk'eq⟩ := List.mem_iff_getElem.mp hmem
      have hadj : G.Adj (p[s]'hs) (p[s + 1]'ht) := path_adj_succ hp ht
      have hadj' : G.Adj (P[k]'hk) (P[k']'hk') := by
        rw [hkeq, hk'eq]; exact hadj
      have hstep := (path_adj_iff hP hk hk').mp hadj'
      exact ⟨k', hk', hk'eq, by omega⟩

/-- **Every rung of the strip spanned by `P` has the same parity as `P`.**

A rung of `({a}, P*, {b})` is a path of `G` from `a` to `b` all of whose vertices lie on `P`, but
it need **not** be `P` itself, so the parity is obtained from `rung_index_parity` rather than
from an identification of the two lists.  This is the clause of `IsStriation` that demands all
rungs be odd. -/
private theorem rung_odd {G : SimpleGraph V} {P p : List V} {a b : V}
    (hP : IsPathFrom G P a b) (hoP : Odd (pathLength P))
    (hr : IsSRung G (({a} : Set V), {v : V | v ∈ SPGT.interior P}, ({b} : Set V)) p) :
    Odd (pathLength p) := by
  obtain ⟨a', b', hpab, ha', hb', -, -, hint⟩ := hr
  simp only [Set.mem_singleton_iff] at ha' hb'
  rw [ha', hb'] at hpab
  have hsub : ∀ v ∈ p, v ∈ P := by
    intro v hv
    by_cases hva : v = a
    · subst hva; exact head_mem hP.2.1
    · by_cases hvb : v = b
      · subst hvb; exact getLast_mem hP.2.2
      · exact interior_subset (hint v ((mem_interior_iff_of_pathFrom hpab).mpr ⟨hv, hva, hvb⟩))
  have hP0 : 0 < P.length := path_length_pos hP.1
  have hp0 : 0 < p.length := path_length_pos hpab.1
  obtain ⟨k, hk, hkeq, hpar⟩ :=
    rung_index_parity hP.1 hP.2.1 hpab.1 hpab.2.1 hsub (p.length - 1) (by omega)
  have h1 : p[p.length - 1]'(by omega) = b := getElem_last_of_getLast? hpab.2.2 hp0
  have h2 : P[P.length - 1]'(by omega) = b := getElem_last_of_getLast? hP.2.2 hP0
  have h3 : P[k]'hk = P[P.length - 1]'(by omega) := by rw [hkeq, h1, h2]
  have h4 : k = P.length - 1 := (List.Nodup.getElem_inj_iff (path_nodup hP.1)).mp h3
  rw [Nat.odd_iff] at hoP ⊢
  simp only [pathLength_eq] at hoP ⊢
  omega

/-! ### Parallelism, read off a knot's edge clause -/

/-- **The knot clause *"the only edges between `V(P)` and `{x, y}` are `ax` and `by`"* says
exactly that the strip spanned by `P` is parallel to the antistrip `({x}, ∅, {y})`.**

`ParallelStripAntistrip` asks for `{a}` complete to `{x} ∪ ∅`, `{b}` complete to `{y} ∪ ∅`,
`{x}` anticomplete to `{b} ∪ P*` and `{y}` anticomplete to `{a} ∪ P*`.  The first two are the
two edges the clause asserts; the last two are its "only" half, since every vertex of `{b} ∪ P*`
lies on `P` and differs from `a`, and every vertex of `{a} ∪ P*` lies on `P` and differs from
`b`. -/
private theorem parallel_of_knot_clause {G : SimpleGraph V} {P : List V} {a b x y : V}
    (hP : IsPathFrom G P a b) (hab : a ≠ b) (hxy : x ≠ y)
    (hcl : ∀ u ∈ P, ∀ w ∈ ({x, y} : Set V),
      (G.Adj u w ↔ ((u = a ∧ w = x) ∨ (u = b ∧ w = y)))) :
    ParallelStripAntistrip G (({a} : Set V), {v : V | v ∈ SPGT.interior P}, ({b} : Set V))
      (({x} : Set V), (∅ : Set V), ({y} : Set V)) := by
  have haP : a ∈ P := head_mem hP.2.1
  have hbP : b ∈ P := getLast_mem hP.2.2
  have hxm : x ∈ ({x, y} : Set V) := by simp
  have hym : y ∈ ({x, y} : Set V) := by simp
  have hax : G.Adj a x := (hcl a haP x hxm).mpr (Or.inl ⟨rfl, rfl⟩)
  have hby : G.Adj b y := (hcl b hbP y hym).mpr (Or.inr ⟨rfl, rfl⟩)
  -- No vertex of `P` other than `a` is adjacent to `x`.
  have hnx : ∀ z ∈ P, z ≠ a → ¬ G.Adj z x := by
    intro z hz hza hadj
    rcases (hcl z hz x hxm).mp hadj with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hza h1
    · exact hxy h2
  -- No vertex of `P` other than `b` is adjacent to `y`.
  have hny : ∀ z ∈ P, z ≠ b → ¬ G.Adj z y := by
    intro z hz hzb hadj
    rcases (hcl z hz y hym).mp hadj with ⟨-, h1⟩ | ⟨h2, -⟩
    · exact hxy h1.symm
    · exact hzb h2
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rintro u hu z hz
    simp only [Set.mem_singleton_iff] at hu
    subst hu
    simp only [Set.union_empty, Set.mem_singleton_iff] at hz
    subst hz
    exact hax
  · rintro u hu z hz
    simp only [Set.mem_singleton_iff] at hu
    subst hu
    simp only [Set.union_empty, Set.mem_singleton_iff] at hz
    subst hz
    exact hby
  · rintro u hu z hz
    simp only [Set.mem_singleton_iff] at hu
    subst hu
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hz
    rcases hz with rfl | hz
    · exact fun hadj => hnx z hbP (Ne.symm hab) hadj.symm
    · have hzi := (mem_interior_iff_of_pathFrom hP).mp hz
      exact fun hadj => hnx z hzi.1 hzi.2.1 hadj.symm
  · rintro u hu z hz
    simp only [Set.mem_singleton_iff] at hu
    subst hu
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at hz
    rcases hz with rfl | hz
    · exact fun hadj => hny z haP hab hadj.symm
    · have hzi := (mem_interior_iff_of_pathFrom hP).mp hz
      exact fun hadj => hny z hzi.1 hzi.2.2 hadj.symm

/-! ### Packaging two strips and two antistrips into a striation -/

/-- **A `2 × 2` striation.**

All the `Fin 2` bookkeeping of `IsStriation` in one place.  The two twist clauses are both
witnessed by the single quadruple `(S₁, S₂, T₁, T₂)`, which is a twist by the first disjunct of
`IsTwist`: `S₁, S₂` **agree** on `T₁` (both parallel to it) and **disagree** on `T₂` (`S₁`
parallel, `S₂` co-parallel).

Stated separately from `exists_striation_of_knot` because it is generic in the four triples: any
future `m = n = 2` striation can be assembled with it. -/
theorem isStriation_two_two {G : SimpleGraph V} (S₁ S₂ T₁ T₂ : Set V × Set V × Set V)
    (hS₁ : IsStrip G S₁) (hS₂ : IsStrip G S₂)
    (hT₁ : IsAntistrip G T₁) (hT₂ : IsAntistrip G T₂)
    (dSS : Disjoint (stripVertices S₁) (stripVertices S₂))
    (dTT : Disjoint (stripVertices T₁) (stripVertices T₂))
    (dST₁₁ : Disjoint (stripVertices S₁) (stripVertices T₁))
    (dST₁₂ : Disjoint (stripVertices S₁) (stripVertices T₂))
    (dST₂₁ : Disjoint (stripVertices S₂) (stripVertices T₁))
    (dST₂₂ : Disjoint (stripVertices S₂) (stripVertices T₂))
    (oS₁ : ∀ p : List V, IsSRung G S₁ p → Odd (pathLength p))
    (oS₂ : ∀ p : List V, IsSRung G S₂ p → Odd (pathLength p))
    (oT₁ : ∀ p : List V, IsSRung Gᶜ T₁ p → Odd (pathLength p))
    (oT₂ : ∀ p : List V, IsSRung Gᶜ T₂ p → Odd (pathLength p))
    (hanti : SPGT.Anticomplete G (stripVertices S₁) (stripVertices S₂))
    (hcomp : SPGT.Complete G (stripVertices T₁) (stripVertices T₂))
    (p₁₁ : ParallelStripAntistrip G S₁ T₁)
    (p₁₂ : ParallelStripAntistrip G S₁ T₂)
    (p₂₁ : ParallelStripAntistrip G S₂ T₁)
    (c₂₂ : CoParallel G S₂ T₂) :
    IsStriation G ![S₁, S₂] ![T₁, T₂] := by
  have e0 : (![S₁, S₂] : Fin 2 → Set V × Set V × Set V) 0 = S₁ := rfl
  have e1 : (![S₁, S₂] : Fin 2 → Set V × Set V × Set V) 1 = S₂ := rfl
  have f0 : (![T₁, T₂] : Fin 2 → Set V × Set V × Set V) 0 = T₁ := rfl
  have f1 : (![T₁, T₂] : Fin 2 → Set V × Set V × Set V) 1 = T₂ := rfl
  have htwist : IsTwist G S₁ S₂ T₁ T₂ :=
    Or.inl ⟨Or.inl ⟨p₁₁, p₂₁⟩, Or.inl ⟨p₁₂, c₂₂⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, le_refl 2, le_refl 2, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rcases fin_two_cases i with rfl | rfl
    · rw [e0]; exact hS₁
    · rw [e1]; exact hS₂
  · intro j
    rcases fin_two_cases j with rfl | rfl
    · rw [f0]; exact hT₁
    · rw [f1]; exact hT₂
  · intro i i' hne
    rcases fin_two_ne i i' hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [e0, e1]; exact dSS
    · rw [e0, e1]; exact dSS.symm
  · intro j j' hne
    rcases fin_two_ne j j' hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [f0, f1]; exact dTT
    · rw [f0, f1]; exact dTT.symm
  · intro i j
    rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases j with rfl | rfl
    · rw [e0, f0]; exact dST₁₁
    · rw [e0, f1]; exact dST₁₂
    · rw [e1, f0]; exact dST₂₁
    · rw [e1, f1]; exact dST₂₂
  · intro i p hr
    rcases fin_two_cases i with rfl | rfl
    · rw [e0] at hr; exact oS₁ p hr
    · rw [e1] at hr; exact oS₂ p hr
  · intro j p hr
    rcases fin_two_cases j with rfl | rfl
    · rw [f0] at hr; exact oT₁ p hr
    · rw [f1] at hr; exact oT₂ p hr
  · intro i i' hlt
    obtain ⟨rfl, rfl⟩ := fin_two_lt i i' hlt
    rw [e0, e1]; exact hanti
  · intro j j' hlt
    obtain ⟨rfl, rfl⟩ := fin_two_lt j j' hlt
    rw [f0, f1]; exact hcomp
  · intro i j
    rcases fin_two_cases i with rfl | rfl <;> rcases fin_two_cases j with rfl | rfl
    · rw [e0, f0]; exact Or.inl p₁₁
    · rw [e0, f1]; exact Or.inl p₁₂
    · rw [e1, f0]; exact Or.inl p₂₁
    · rw [e1, f1]; exact Or.inr c₂₂
  · intro i i' hlt
    obtain ⟨rfl, rfl⟩ := fin_two_lt i i' hlt
    exact ⟨0, 1, by decide, by rw [e0, e1, f0, f1]; exact htwist⟩
  · intro j j' hlt
    obtain ⟨rfl, rfl⟩ := fin_two_lt j j' hlt
    exact ⟨0, 1, by decide, by rw [e0, e1, f0, f1]; exact htwist⟩

/-! ### The main result -/

/-- **A knot whose two antipaths have length `1` and whose two paths have odd length yields a
striation, with `m = n = 2`.**

This is *"By hypothesis it is degenerate, and hence there is a striation in `G`"* (9.6, printed
p. 55), on the assumption — supplied elsewhere — that a degenerate `K₄`-appearance is a knot of
this shape.

The two strips are the paths split as `({aᵢ}, Pᵢ*, {bᵢ})`; the two antistrips are the antipaths,
which have length `1` and hence empty interior, split as `({xⱼ}, ∅, {yⱼ})`.  The knot's clause
*"the only edges between `V(P₂)` and `{x₂, y₂}` are `a₂y₂` and `b₂x₂`"* is the reversed pattern
of the other three, which is precisely what makes `(S₂, T₂)` **co-parallel** while the other
three pairs are parallel — and hence what makes `(S₁, S₂, T₁, T₂)` a twist. -/
theorem exists_striation_of_knot (G : SimpleGraph V)
    {P₁ P₂ Q₁ Q₂ : List V} (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hQ₁ : pathLength Q₁ = 1) (hQ₂ : pathLength Q₂ = 1)
    (hoP₁ : Odd (pathLength P₁)) (hoP₂ : Odd (pathLength P₂)) :
    ∃ (m n : ℕ) (S : Fin m → Set V × Set V × Set V)
      (T : Fin n → Set V × Set V × Set V), IsStriation G S T := by
  obtain ⟨a₁, b₁, a₂, b₂, x₁, y₁, x₂, y₂,
    hP₁, hP₂, hQ₁a, hQ₂a, d12, d1Q1, d1Q2, d2Q1, d2Q2, dQ12,
    hlP₁, hlP₂, -, -, hanti, hcomp, c11, c12, c21, c22, -, -, -, -⟩ := hknot
  -- The antipaths are paths of the complement.
  have hQ₁p : IsPathFrom Gᶜ Q₁ x₁ y₁ := hQ₁a
  have hQ₂p : IsPathFrom Gᶜ Q₂ x₂ y₂ := hQ₂a
  -- Distinctness of the four pairs of ends.
  have ha₁b₁ : a₁ ≠ b₁ := isPathFrom_ends_ne hP₁ hlP₁
  have ha₂b₂ : a₂ ≠ b₂ := isPathFrom_ends_ne hP₂ hlP₂
  have hx₁y₁ : x₁ ≠ y₁ := isPathFrom_ends_ne hQ₁p (by omega)
  have hx₂y₂ : x₂ ≠ y₂ := isPathFrom_ends_ne hQ₂p (by omega)
  -- The antipaths have empty interior, so the antistrips' middle sets are `∅`.
  have hZ₁ : {v : V | v ∈ SPGT.interior Q₁} = (∅ : Set V) := interior_eq_empty_of_length_one hQ₁
  have hZ₂ : {v : V | v ∈ SPGT.interior Q₂} = (∅ : Set V) := interior_eq_empty_of_length_one hQ₂
  -- Vertex sets of the four triples.
  have hV₁ : stripVertices (({a₁} : Set V), {v : V | v ∈ SPGT.interior P₁}, ({b₁} : Set V))
      = {v : V | v ∈ P₁} := stripVertices_pathTriple hP₁ rfl
  have hV₂ : stripVertices (({a₂} : Set V), {v : V | v ∈ SPGT.interior P₂}, ({b₂} : Set V))
      = {v : V | v ∈ P₂} := stripVertices_pathTriple hP₂ rfl
  have hW₁ : stripVertices (({x₁} : Set V), (∅ : Set V), ({y₁} : Set V))
      = {v : V | v ∈ Q₁} := stripVertices_pathTriple hQ₁p hZ₁.symm
  have hW₂ : stripVertices (({x₂} : Set V), (∅ : Set V), ({y₂} : Set V))
      = {v : V | v ∈ Q₂} := stripVertices_pathTriple hQ₂p hZ₂.symm
  -- The reversed clause, for the co-parallel pair `(S₂, T₂)`.
  have c22' : ∀ u ∈ P₂, ∀ w ∈ ({y₂, x₂} : Set V),
      (G.Adj u w ↔ ((u = a₂ ∧ w = y₂) ∨ (u = b₂ ∧ w = x₂))) := by
    intro u hu w hw
    exact c22 u hu w (by rw [Set.pair_comm x₂ y₂]; exact hw)
  refine ⟨2, 2,
    ![(({a₁} : Set V), {v : V | v ∈ SPGT.interior P₁}, ({b₁} : Set V)),
      (({a₂} : Set V), {v : V | v ∈ SPGT.interior P₂}, ({b₂} : Set V))],
    ![(({x₁} : Set V), (∅ : Set V), ({y₁} : Set V)),
      (({x₂} : Set V), (∅ : Set V), ({y₂} : Set V))], ?_⟩
  refine isStriation_two_two _ _ _ _
    (isStrip_of_pathFrom hP₁ ha₁b₁ rfl) (isStrip_of_pathFrom hP₂ ha₂b₂ rfl)
    (isStrip_of_pathFrom hQ₁p hx₁y₁ hZ₁.symm) (isStrip_of_pathFrom hQ₂p hx₂y₂ hZ₂.symm)
    ?_ ?_ ?_ ?_ ?_ ?_
    (fun p hr => rung_odd hP₁ hoP₁ hr) (fun p hr => rung_odd hP₂ hoP₂ hr)
    (fun p hr => antirung_odd hx₁y₁ hr) (fun p hr => antirung_odd hx₂y₂ hr)
    ?_ ?_
    (parallel_of_knot_clause hP₁ ha₁b₁ hx₁y₁ c11)
    (parallel_of_knot_clause hP₁ ha₁b₁ hx₂y₂ c12)
    (parallel_of_knot_clause hP₂ ha₂b₂ hx₁y₁ c21)
    (parallel_of_knot_clause hP₂ ha₂b₂ (Ne.symm hx₂y₂) c22')
  · rw [hV₁, hV₂, Set.disjoint_left]; exact fun v hv => d12 v hv
  · rw [hW₁, hW₂, Set.disjoint_left]; exact fun v hv => dQ12 v hv
  · rw [hV₁, hW₁, Set.disjoint_left]; exact fun v hv => d1Q1 v hv
  · rw [hV₁, hW₂, Set.disjoint_left]; exact fun v hv => d1Q2 v hv
  · rw [hV₂, hW₁, Set.disjoint_left]; exact fun v hv => d2Q1 v hv
  · rw [hV₂, hW₂, Set.disjoint_left]; exact fun v hv => d2Q2 v hv
  · rw [hV₁, hV₂]; exact hanti
  · rw [hW₁, hW₂]; exact hcomp

end Workspace.ProofLemmas.StriationFromKnot
