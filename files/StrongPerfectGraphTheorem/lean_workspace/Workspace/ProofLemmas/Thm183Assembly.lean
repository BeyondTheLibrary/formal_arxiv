import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.Thm183EvenLength
import Workspace.ProofLemmas.Thm183LineEvenCase
import Workspace.ProofLemmas.Thm183LineOddCase
import Workspace.ProofLemmas.Thm183Lines

/-!
# 18.3, second conclusion, and the assembly of all three

The printed proof of **18.3** (`paper/proofs/18_3.md`, published page 110) proves the second
conclusion by a two-way case split on the ends of a line:

> *"Let us say a line is a maximal subpath `P'` of `P` such that no internal vertex of `P'` is
> `Y`-complete.  Let `P'` be a line of length `≥ 2`, and assume first that both ends of `P'` are
> `Y`-complete.  … So in this case `P'` has even length.  We may therefore assume that an end of
> `P'` is not `Y`-complete, and from the maximality of `P'`, any such end is either `p₁` or
> `pₙ`, and we may assume it is `pₙ` from the symmetry.  … Consequently `P'` is odd, as
> required."*

The two branches are `Thm183LineEvenCase` and `Thm183LineOddCase` (the latter mirrored by
`Thm183Lines.line_odd_of_first_end_not_YComplete`).  What is left, and is what this module does,
is the bookkeeping the paper performs silently:

* a subpath of `P` is a contiguous stretch `pᵢ-⋯-pⱼ` of it (`hqs` below);
* *"from the maximality of `P'`, any such end is either `p₁` or `pₙ`"* — proved by exhibiting
  the one-step extension of the line that maximality forbids (`end_left`, `end_right`);
* the count *"the number of ends of `P'` that belong to `{p₁,pₙ}` and are not `Y`-complete"* is
  `0` in the first branch and `1` in the second;
* the fourth combination — both ends not `Y`-complete — makes `P'` the whole of `P` and leaves
  `P` with no `Y`-complete vertex, contrary to *"at least two vertices of `P` are
  `Y`-complete"*.

`thm_18_3_full` then assembles the three conclusions into exactly the shape of the frozen
`Workspace.Statements.S18.SPGT.thm_18_3` (see `FIXES.md` §F7 for the one repaired hypothesis
`2 ≤ pathLength q`, which is the printed proof's own *"a line of length `≥ 2`"*).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm183Assembly

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Small list facts about the stretches `pᵢ-⋯-pⱼ` -/

/-- Every stretch of `p` is a contiguous block of `p`. -/
private theorem slice_infix (p : List V) (i m : ℕ) : (p.drop i).take m <:+: p := by
  refine ⟨p.take i, (p.drop i).drop m, ?_⟩
  rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

/-- A contiguous block of `p` is a stretch `pᵢ-⋯-pⱼ` of it. -/
private theorem infix_eq_slice {p q : List V} (h : q <:+: p) :
    ∃ i : ℕ, i + q.length ≤ p.length ∧ q = (p.drop i).take q.length := by
  obtain ⟨s, t, hst⟩ := h
  refine ⟨s.length, ?_, ?_⟩
  · have : p.length = s.length + q.length + t.length := by
      rw [← hst]; simp [List.length_append]; omega
    omega
  · have hp : p = s ++ (q ++ t) := by rw [← hst, List.append_assoc]
    rw [hp, List.drop_left, List.take_left]

/-- Transporting an index equality through `List.getElem` without asking `rw` to construct a
dependent motive. -/
private theorem getElem_congr_idx {α : Type*} (l : List α) {a b : ℕ}
    (ha : a < l.length) (hb : b < l.length) (h : a = b) : l[a]'ha = l[b]'hb := by
  subst h
  rfl

/-! ## "at least two vertices of `P` are `Y`-complete" -/

/-- If every `Y`-complete vertex of `P` is one fixed vertex `z`, then `P` has at most one
`Y`-complete vertex — contrary to 18.3's hypothesis. -/
theorem not_unique_YComplete {G : SimpleGraph V} {Y : Set V} {p : List V} {z : V}
    (h2 : 2 ≤ {w : V | w ∈ p ∧ VertexComplete G w Y}.ncard)
    (hall : ∀ w ∈ p, VertexComplete G w Y → w = z) : False := by
  have hsub : {w : V | w ∈ p ∧ VertexComplete G w Y} ⊆ ({z} : Set V) :=
    fun w hw => hall w hw.1 hw.2
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_singleton] at hle
  omega

/-! ## The second conclusion -/

/-- **18.3, second conclusion** (repaired; see `FIXES.md` §F7).

*"let `P'` be a maximal subpath of `P` such that none of its internal vertices are `Y`-complete
[and of length `≥ 2`].  Then the length of `P'` has the same parity as the number of ends of
`P'` that belong to `{p₁,pₙ}` and are not `Y`-complete."* -/
theorem line_parity
    (G : SimpleGraph V) (hG5 : InF5 G) (X Y : Set V)
    (hXY : Disjoint X Y) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXa : AnticonnectedSet G X) (hYa : AnticonnectedSet G Y)
    (hcompl : Complete G X Y)
    (p : List V) (p₁ pₙ : V) (hp : IsPathList G p)
    (hpXY : ∀ w ∈ p, w ∉ X ∪ Y) (hn : 5 ≤ p.length)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pₙ)
    (hXuniq : ∀ w ∈ p, (VertexComplete G w X ↔ (w = p₁ ∨ w = pₙ)))
    (h2 : 2 ≤ {w : V | w ∈ p ∧ VertexComplete G w Y}.ncard)
    (q : List V) (a b : V) (hqp : q <:+: p) (hq : IsPathFrom G q a b)
    (hqint : ∀ w ∈ SPGT.interior q, ¬ VertexComplete G w Y)
    (hqmax : ∀ r : List V, r <:+: p →
      (∀ w ∈ SPGT.interior r, ¬ VertexComplete G w Y) → q <:+: r → r = q)
    (hq2 : 2 ≤ pathLength q) :
    pathLength q % 2 =
      {w : V | (w = a ∨ w = b) ∧ (w = p₁ ∨ w = pₙ) ∧
        ¬ VertexComplete G w Y}.ncard % 2 := by
  classical
  have h0lt : 0 < p.length := by omega
  have hLlt : p.length - 1 < p.length := by omega
  have hp0 : p[0]'h0lt = p₁ := PathBasics.getElem_zero_of_head? hhead h0lt
  have hpL : p[p.length - 1]'hLlt = pₙ := PathBasics.getElem_last_of_getLast? hlast h0lt
  -- ### The line is a stretch `pᵢ-⋯-pⱼ` of `P`.
  have hqlen : 2 ≤ pathLength q := hq2
  rw [PathBasics.pathLength_eq] at hqlen
  obtain ⟨i, hile, hqs⟩ := infix_eq_slice hqp
  have hi : i < p.length := by omega
  set j : ℕ := i + q.length - 1 with hjdef
  have hij : i < j := by omega
  have hj : j < p.length := by omega
  have hql : q.length = j - i + 1 := by omega
  have hpl : pathLength q = j - i := by rw [PathBasics.pathLength_eq]; omega
  have hqs' : q = (p.drop i).take (j - i + 1) := by rw [hqs, hql]
  have hslice : IsPathFrom G q (p[i]'hi) (p[j]'hj) := by
    rw [hqs']; exact PathBasics.isPathFrom_slice hp hij hj
  have hA : a = p[i]'hi := Option.some_injective _ (hq.2.1.symm.trans hslice.2.1)
  have hB : b = p[j]'hj := Option.some_injective _ (hq.2.2.symm.trans hslice.2.2)
  -- The interior of the line, in index form.
  have hIint : ∀ (k : ℕ) (hk : k < p.length), i < k → k < j →
      ¬ VertexComplete G (p[k]'hk) Y := by
    intro k hk h1 h2' hc
    refine hqint (p[k]'hk) ?_ hc
    rw [hqs']
    exact (PathBasics.mem_interior_slice_iff hp hij hj).mpr ⟨k, hk, h1, h2', rfl⟩
  -- ### *"from the maximality of `P'`, any such end is either `p₁` or `pₙ`"* — left end.
  have end_left : ¬ VertexComplete G (p[i]'hi) Y → i = 0 := by
    intro hnc
    by_contra hi0
    have hipos : 0 < i := Nat.pos_of_ne_zero hi0
    have hii : i - 1 + 1 = i := by omega
    have hi1 : i - 1 < p.length := by omega
    have hd : p.drop (i - 1) = (p[i - 1]'hi1) :: p.drop i := by
      rw [List.drop_eq_getElem_cons hi1, hii]
    have hrq : (p.drop (i - 1)).take (j - (i - 1) + 1) = (p[i - 1]'hi1) :: q := by
      rw [hd, show j - (i - 1) + 1 = (j - i + 1) + 1 by omega, List.take_succ_cons, hqs']
    have hrint : ∀ w ∈ SPGT.interior ((p.drop (i - 1)).take (j - (i - 1) + 1)),
        ¬ VertexComplete G w Y := by
      intro w hw
      obtain ⟨k, hk, h1, h2', rfl⟩ :=
        (PathBasics.mem_interior_slice_iff hp (by omega : i - 1 < j) hj).mp hw
      rcases Nat.lt_or_ge i k with hlt | hge
      · exact hIint k hk hlt h2'
      · have hki : k = i := by omega
        subst hki; exact hnc
    have hqr : q <:+: (p.drop (i - 1)).take (j - (i - 1) + 1) :=
      ⟨[p[i - 1]'hi1], [], by rw [hrq]; simp⟩
    have heq := hqmax _ (slice_infix p _ _) hrint hqr
    have hlen1 : ((p.drop (i - 1)).take (j - (i - 1) + 1)).length = j - (i - 1) + 1 :=
      PathBasics.length_slice p (by omega) hj
    rw [heq, hql] at hlen1
    omega
  -- ### … and right end.
  have end_right : ¬ VertexComplete G (p[j]'hj) Y → j = p.length - 1 := by
    intro hnc
    by_contra hjn
    have hj1 : j + 1 < p.length := by omega
    have hrint : ∀ w ∈ SPGT.interior ((p.drop i).take (j + 1 - i + 1)),
        ¬ VertexComplete G w Y := by
      intro w hw
      obtain ⟨k, hk, h1, h2', rfl⟩ :=
        (PathBasics.mem_interior_slice_iff hp (by omega : i < j + 1) hj1).mp hw
      rcases Nat.lt_or_ge k j with hlt | hge
      · exact hIint k hk h1 hlt
      · have hkj : k = j := by omega
        subst hkj; exact hnc
    have hqr : q <:+: (p.drop i).take (j + 1 - i + 1) := by
      refine ⟨[], ((p.drop i).drop (j - i + 1)).take 1, ?_⟩
      rw [List.nil_append, hqs', show j + 1 - i + 1 = (j - i + 1) + 1 by omega]
      exact (List.take_add (l := p.drop i) (i := j - i + 1) (j := 1)).symm
    have heq := hqmax _ (slice_infix p _ _) hrint hqr
    have hlen1 : ((p.drop i).take (j + 1 - i + 1)).length = j + 1 - i + 1 :=
      PathBasics.length_slice p (by omega) hj1
    rw [heq, hql] at hlen1
    omega
  -- ### The four combinations of the two ends.
  by_cases hca : VertexComplete G (p[i]'hi) Y <;> by_cases hcb : VertexComplete G (p[j]'hj) Y
  · -- *"assume first that both ends of `P'` are `Y`-complete … `P'` has even length"*
    have hev := Thm183LineEvenCase.line_even_of_both_ends_YComplete G hG5 X Y hXY hXa hYa
      hcompl p p₁ pₙ hp hpXY hn hhead hlast hXuniq i j (by omega) hj hIint hca hcb
    have hset : {w : V | (w = a ∨ w = b) ∧ (w = p₁ ∨ w = pₙ) ∧
        ¬ VertexComplete G w Y} = (∅ : Set V) := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      rintro (rfl | rfl) -
      · rw [hA]; exact fun hcon => hcon hca
      · rw [hB]; exact fun hcon => hcon hcb
    rw [hset, Set.ncard_empty, hpl, Nat.even_iff.mp hev]
  · -- the non-`Y`-complete end is the right one, so it is `pₙ`: *"we may assume it is `pₙ`"*
    have hjE : j = p.length - 1 := end_right hcb
    have hbn : b = pₙ :=
      hB.trans ((getElem_congr_idx p hj hLlt hjE).trans hpL)
    have hipos : 0 < i := by
      by_contra hi0
      have hi0' : i = 0 := by omega
      refine not_unique_YComplete h2 (z := p₁) ?_
      intro w hw hwY
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · exact hp0
      · rcases Nat.lt_or_ge k j with hlt | hge
        · exact absurd hwY (hIint k hk (by omega) hlt)
        · have : k = j := by omega
          subst this; exact absurd hwY hcb
    have hodd := Thm183LineOddCase.line_odd_of_last_end_not_YComplete G hG5 X Y hXY hXne hYne
      hXa hYa hcompl p p₁ pₙ hp hpXY hn hhead hlast hXuniq i hipos (by omega)
      (fun k hk h1 h2' => hIint k hk h1 (by omega)) hca
      (by
        rw [← hpL, getElem_congr_idx p hLlt hj hjE.symm]
        exact hcb)
      (by
        by_contra hcon
        push Not at hcon
        refine not_unique_YComplete h2 (z := p[i]'hi) ?_
        intro w hw hwY
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
        rcases Nat.lt_or_ge k i with hlt | hge
        · exact absurd hwY (hcon k hk hlt)
        · rcases Nat.eq_or_lt_of_le hge with heq | hlt2
          · exact getElem_congr_idx p hk hi heq.symm
          · rcases Nat.lt_or_ge k j with hlt3 | hge3
            · exact absurd hwY (hIint k hk hlt2 hlt3)
            · have : k = j := by omega
              subst this; exact absurd hwY hcb)
    have hset : {w : V | (w = a ∨ w = b) ∧ (w = p₁ ∨ w = pₙ) ∧
        ¬ VertexComplete G w Y} = ({b} : Set V) := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨rfl | rfl, -, hnc⟩
        · exact absurd (hA ▸ hca) hnc
        · rfl
      · rintro rfl
        exact ⟨Or.inr rfl, Or.inr hbn, by rw [hB]; exact hcb⟩
    rw [hset, Set.ncard_singleton, hpl]
    have : p.length - 1 - i = j - i := by omega
    rw [← this]
    exact Nat.odd_iff.mp hodd
  · -- the non-`Y`-complete end is the left one, so it is `p₁`
    have hiE : i = 0 := end_left hca
    have han : a = p₁ := by rw [hA]; exact hiE ▸ hp0
    have hjlt : j + 1 < p.length := by
      by_contra hjn
      have hjE : j = p.length - 1 := by omega
      refine not_unique_YComplete h2 (z := pₙ) ?_
      intro w hw hwY
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
      rcases Nat.lt_or_ge k j with hlt | hge
      · rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · exact absurd hwY (hiE ▸ hca)
        · exact absurd hwY (hIint k hk (by omega) hlt)
      · have hkj : k = j := by omega
        exact (getElem_congr_idx p hk hLlt (hkj.trans hjE)).trans hpL
    have hodd := Thm183Lines.line_odd_of_first_end_not_YComplete G hG5 X Y hXY hXne hYne
      hXa hYa hcompl p p₁ pₙ hp hpXY hn hhead hlast hXuniq j (by omega) hjlt
      (fun k hk h1 h2' => hIint k hk (by omega) h2') hcb
      (by
        rw [← hp0, getElem_congr_idx p h0lt hi hiE.symm]
        exact hca)
      (by
        by_contra hcon
        push Not at hcon
        refine not_unique_YComplete h2 (z := p[j]'hj) ?_
        intro w hw hwY
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
        rcases Nat.lt_or_ge j k with hlt | hge
        · exact absurd hwY (hcon k hk hlt)
        · rcases Nat.eq_or_lt_of_le hge with heq | hlt2
          · exact getElem_congr_idx p hk hj heq
          · rcases Nat.eq_zero_or_pos k with rfl | hkpos
            · exact absurd hwY (hiE ▸ hca)
            · exact absurd hwY (hIint k hk (by omega) hlt2))
    have hset : {w : V | (w = a ∨ w = b) ∧ (w = p₁ ∨ w = pₙ) ∧
        ¬ VertexComplete G w Y} = ({a} : Set V) := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨rfl | rfl, -, hnc⟩
        · rfl
        · exact absurd (hB ▸ hcb) hnc
      · rintro rfl
        exact ⟨Or.inl rfl, Or.inl han, by rw [hA]; exact hca⟩
    rw [hset, Set.ncard_singleton, hpl, hiE]
    simpa using Nat.odd_iff.mp hodd
  · -- both ends fail to be `Y`-complete: then `P' = P`, and `P` has no `Y`-complete vertex
    exfalso
    have hiE : i = 0 := end_left hca
    have hjE : j = p.length - 1 := end_right hcb
    refine not_unique_YComplete h2 (z := p₁) ?_
    intro w hw hwY
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exact hp0
    · rcases Nat.lt_or_ge k j with hlt | hge
      · exact absurd hwY (hIint k hk (by omega) hlt)
      · have : k = j := by omega
        subst this; exact absurd hwY hcb

/-! ## The full statement -/

/-- **18.3**, in exactly the shape of the frozen
`Workspace.Statements.S18.SPGT.thm_18_3` (repaired second conjunct; `FIXES.md` §F7). -/
theorem thm_18_3_full (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V)
    (hXY : Disjoint X Y) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXa : AnticonnectedSet G X) (hYa : AnticonnectedSet G Y)
    (hcompl : Complete G X Y)
    (p : List V) (p₁ pₙ : V) (hp : IsPathList G p)
    (hpXY : ∀ w ∈ p, w ∉ X ∪ Y) (hn : 5 ≤ p.length)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pₙ)
    (hXuniq : ∀ w ∈ p, (VertexComplete G w X ↔ (w = p₁ ∨ w = pₙ))) :
    Even (pathLength p) ∧
    (2 ≤ {w : V | w ∈ p ∧ VertexComplete G w Y}.ncard →
      ((∀ (q : List V) (a b : V), q <:+: p → IsPathFrom G q a b →
          (∀ w ∈ SPGT.interior q, ¬ VertexComplete G w Y) →
          (∀ r : List V, r <:+: p →
            (∀ w ∈ SPGT.interior r, ¬ VertexComplete G w Y) → q <:+: r → r = q) →
          2 ≤ pathLength q →
          pathLength q % 2 =
            {w : V | (w = a ∨ w = b) ∧ (w = p₁ ∨ w = pₙ) ∧
              ¬ VertexComplete G w Y}.ncard % 2) ∧
        {e : Sym2 V | ∃ u ∈ p, ∃ v ∈ p, e = s(u, v) ∧ EdgeComplete G Y u v}.ncard % 2 =
          {w : V | (w = p₁ ∨ w = pₙ) ∧ VertexComplete G w Y}.ncard % 2)) := by
  have hG5 : InF5 G := hG.1.1
  have hpX : ∀ w ∈ p, w ∉ X := fun w hw hwX => hpXY w hw (Set.mem_union_left _ hwX)
  -- *"Then `P` has even length"* — the opening sentence, by 13.6.
  have hev : Even (pathLength p) :=
    Thm183EvenLength.even_pathLength_of_ends_only_XComplete G hG5 X hXa p p₁ pₙ hp hpX hn
      hhead hlast hXuniq
  refine ⟨hev, fun h2 => ⟨?_, ?_⟩⟩
  · exact fun q a b hqp hq hqint hqmax hq2 =>
      line_parity G hG5 X Y hXY hXne hYne hXa hYa hcompl p p₁ pₙ hp hpXY hn hhead hlast
        hXuniq h2 q a b hqp hq hqint hqmax hq2
  · exact Thm183Lines.yEdges_parity G hG5 X Y hXY hXne hYne hXa hYa hcompl p p₁ pₙ hp hpXY hn
      hhead hlast hXuniq hev h2

end Workspace.ProofLemmas.Thm183Assembly
