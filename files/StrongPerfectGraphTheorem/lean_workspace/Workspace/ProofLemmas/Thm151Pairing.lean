import Mathlib
import Workspace.Types.Core
import Workspace.Types.DoubleDiamond
import Workspace.Types.Classes
import Workspace.ProofLemmas.LK33eAppearance

/-!
# The last two sentences of the printed proof of 15.1

PAPER (printed p. 92): *"So there are exactly two edges between `{a₂, a₂'}` and `{b₂, b₂'}`,
forming a 2-edge matching.  There are two possible pairings; in one case the subgraph induced on
these eight vertices is a double diamond, and in the other it is `L(K₃,₃ \ e)`.  In both cases
this contradicts that `G ∈ F₆`."*

The eight vertices are `b₁, b₁', a₁, a₁', a₂, a₂', b₂, b₂'`.  At the point where the proof
reaches this sentence it has established every adjacency among them except the two matching
edges; those are collected below as `Config`, and the two pairings are the two extra
hypotheses.

`doubleDiamond_of_pairing_one` is the first case.  The second case is *not* a double diamond
under any labelling of the eight vertices — machine-checked by
`scripts/check_15_1_final_configuration.py`:

```
pairing 1: |E| = 14     double diamond : YES     L(K33 - e) : NO
pairing 2: |E| = 14     double diamond : NO      L(K33 - e) : YES
```

so it has to be discharged through the `L(H)` clause of `F₃` instead.

`config_ne` collects the twenty-eight disequalities among the eight vertices.  All of them are
independent of which pairing holds, so the second case will reuse it verbatim.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Workspace.ProofLemmas.Thm151Pairing

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*}

/-- Everything the proof of 15.1 knows about the eight vertices before the final case split:
the two interior edges, the two nonadjacent pairs, `B₁` complete to `B₂`, the three induced
paths `P = b₁-a₁-a₁'-b₁'`, `R = b₁-a₂-a₂'-b₁'` and `b₂-a₁-a₁'-b₂'`, and `A₁` anticomplete to
`A₂`. -/
structure Config (G : SimpleGraph V) (b₁ b₁' a₁ a₁' a₂ a₂' b₂ b₂' : V) : Prop where
  a₁a₁' : G.Adj a₁ a₁'
  a₂a₂' : G.Adj a₂ a₂'
  nb₁b₁' : ¬ G.Adj b₁ b₁'
  nb₂b₂' : ¬ G.Adj b₂ b₂'
  b₁b₂ : G.Adj b₁ b₂
  b₁b₂' : G.Adj b₁ b₂'
  b₁'b₂ : G.Adj b₁' b₂
  b₁'b₂' : G.Adj b₁' b₂'
  b₁a₁ : G.Adj b₁ a₁
  a₁'b₁' : G.Adj a₁' b₁'
  nb₁a₁' : ¬ G.Adj b₁ a₁'
  na₁b₁' : ¬ G.Adj a₁ b₁'
  b₁a₂ : G.Adj b₁ a₂
  a₂'b₁' : G.Adj a₂' b₁'
  nb₁a₂' : ¬ G.Adj b₁ a₂'
  na₂b₁' : ¬ G.Adj a₂ b₁'
  b₂a₁ : G.Adj b₂ a₁
  a₁'b₂' : G.Adj a₁' b₂'
  nb₂a₁' : ¬ G.Adj b₂ a₁'
  na₁b₂' : ¬ G.Adj a₁ b₂'
  na₁a₂ : ¬ G.Adj a₁ a₂
  na₁a₂' : ¬ G.Adj a₁ a₂'
  na₁'a₂ : ¬ G.Adj a₁' a₂
  na₁'a₂' : ¬ G.Adj a₁' a₂'

private theorem ne_of_adj_not_adj {G : SimpleGraph V} {x y z : V}
    (hx : G.Adj x z) (hy : ¬ G.Adj y z) : x ≠ y := by
  rintro rfl; exact hy hx

/-- The eight vertices are pairwise distinct.  Every derivation uses only `Config`, so it is
valid for both pairings. -/
theorem config_ne {G : SimpleGraph V} {b₁ b₁' a₁ a₁' a₂ a₂' b₂ b₂' : V}
    (h : Config G b₁ b₁' a₁ a₁' a₂ a₂' b₂ b₂') :
    b₁ ≠ b₂ ∧ b₁ ≠ a₁ ∧ b₁ ≠ a₂ ∧ b₁ ≠ b₂' ∧ b₁ ≠ b₁' ∧ b₁ ≠ a₁' ∧ b₁ ≠ a₂' ∧
    b₂ ≠ a₁ ∧ b₂ ≠ a₂ ∧ b₂ ≠ b₂' ∧ b₂ ≠ b₁' ∧ b₂ ≠ a₁' ∧ b₂ ≠ a₂' ∧
    a₁ ≠ a₂ ∧ a₁ ≠ b₂' ∧ a₁ ≠ b₁' ∧ a₁ ≠ a₁' ∧ a₁ ≠ a₂' ∧
    a₂ ≠ b₂' ∧ a₂ ≠ b₁' ∧ a₂ ≠ a₁' ∧ a₂ ≠ a₂' ∧
    b₂' ≠ b₁' ∧ b₂' ≠ a₁' ∧ b₂' ≠ a₂' ∧
    b₁' ≠ a₁' ∧ b₁' ≠ a₂' ∧ a₁' ≠ a₂' := by
  have e1 : b₁ ≠ b₂ := G.ne_of_adj h.b₁b₂
  have e2 : b₁ ≠ a₁ := G.ne_of_adj h.b₁a₁
  have e3 : b₁ ≠ a₂ := G.ne_of_adj h.b₁a₂
  have e4 : b₁ ≠ b₂' := G.ne_of_adj h.b₁b₂'
  have e5 : b₁ ≠ b₁' := ne_of_adj_not_adj h.b₁a₁ (fun hc => h.na₁b₁' hc.symm)
  have e6 : b₁ ≠ a₁' := ne_of_adj_not_adj h.b₁b₂ (fun hc => h.nb₂a₁' hc.symm)
  have e7 : b₁ ≠ a₂' := ne_of_adj_not_adj h.b₁a₁ (fun hc => h.na₁a₂' hc.symm)
  have e8 : b₂ ≠ a₁ := G.ne_of_adj h.b₂a₁
  have e9 : b₂ ≠ a₂ := ne_of_adj_not_adj h.b₂a₁ (fun hc => h.na₁a₂ hc.symm)
  have e10 : b₂ ≠ b₂' := ne_of_adj_not_adj h.b₂a₁ (fun hc => h.na₁b₂' hc.symm)
  have e11 : b₂ ≠ b₁' := (G.ne_of_adj h.b₁'b₂).symm
  have e12 : b₂ ≠ a₁' := ne_of_adj_not_adj h.b₁b₂.symm (fun hc => h.nb₁a₁' hc.symm)
  have e13 : b₂ ≠ a₂' := ne_of_adj_not_adj h.b₁b₂.symm (fun hc => h.nb₁a₂' hc.symm)
  have e14 : a₁ ≠ a₂ := ne_of_adj_not_adj h.a₁a₁' (fun hc => h.na₁'a₂ hc.symm)
  have e15 : a₁ ≠ b₂' := ne_of_adj_not_adj h.b₂a₁.symm (fun hc => h.nb₂b₂' hc.symm)
  have e16 : a₁ ≠ b₁' := ne_of_adj_not_adj h.b₁a₁.symm (fun hc => h.nb₁b₁' hc.symm)
  have e17 : a₁ ≠ a₁' := G.ne_of_adj h.a₁a₁'
  have e18 : a₁ ≠ a₂' := ne_of_adj_not_adj h.a₁a₁' (fun hc => h.na₁'a₂' hc.symm)
  have e19 : a₂ ≠ b₂' := (ne_of_adj_not_adj h.b₁'b₂'.symm h.na₂b₁').symm
  have e20 : a₂ ≠ b₁' := ne_of_adj_not_adj h.b₁a₂.symm (fun hc => h.nb₁b₁' hc.symm)
  have e21 : a₂ ≠ a₁' := ne_of_adj_not_adj h.a₂a₂' (fun hc => h.na₁'a₂' hc)
  have e22 : a₂ ≠ a₂' := G.ne_of_adj h.a₂a₂'
  have e23 : b₂' ≠ b₁' := (G.ne_of_adj h.b₁'b₂').symm
  have e24 : b₂' ≠ a₁' := (G.ne_of_adj h.a₁'b₂').symm
  have e25 : b₂' ≠ a₂' := ne_of_adj_not_adj h.b₁b₂'.symm (fun hc => h.nb₁a₂' hc.symm)
  have e26 : b₁' ≠ a₁' := (G.ne_of_adj h.a₁'b₁').symm
  have e27 : b₁' ≠ a₂' := (G.ne_of_adj h.a₂'b₁').symm
  have e28 : a₁' ≠ a₂' := ne_of_adj_not_adj h.a₁a₁'.symm (fun hc => h.na₁a₂' hc.symm)
  exact ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18,
    e19, e20, e21, e22, e23, e24, e25, e26, e27, e28⟩

/-- The same twenty-eight facts, packaged as a `Nodup` for `IsDoubleDiamond`. -/
theorem config_nodup {G : SimpleGraph V} {b₁ b₁' a₁ a₁' a₂ a₂' b₂ b₂' : V}
    (h : Config G b₁ b₁' a₁ a₁' a₂ a₂' b₂ b₂') :
    ([b₁, b₂, a₁, a₂, b₂', b₁', a₁', a₂'] : List V).Nodup := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18,
    e19, e20, e21, e22, e23, e24, e25, e26, e27, e28⟩ := config_ne h
  simp [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18,
    e19, e20, e21, e22, e23, e24, e25, e26, e27, e28]

/-- **The first pairing.**  `a₂b₂` and `a₂'b₂'` are the two edges of the matching; the eight
vertices then induce a double diamond, with

`(a₁,a₂,a₃,a₄,b₁,b₂,b₃,b₄) = (b₁, b₂, a₁, a₂, b₂', b₁', a₁', a₂')`

— the labelling produced by `scripts/check_15_1_final_configuration.py`. -/
theorem doubleDiamond_of_pairing_one {G : SimpleGraph V} {b₁ b₁' a₁ a₁' a₂ a₂' b₂ b₂' : V}
    (h : Config G b₁ b₁' a₁ a₁' a₂ a₂' b₂ b₂')
    (ha₂b₂ : G.Adj a₂ b₂) (ha₂'b₂' : G.Adj a₂' b₂')
    (hna₂b₂' : ¬ G.Adj a₂ b₂') (hna₂'b₂ : ¬ G.Adj a₂' b₂) :
    ∃ x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : V, IsDoubleDiamond G x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ := by
  refine ⟨b₁, b₂, a₁, a₂, b₂', b₁', a₁', a₂', config_nodup h, ?_, ?_, ?_, ?_⟩
  · exact ⟨h.b₁b₂, h.b₁a₁, h.b₁a₂, h.b₂a₁, ha₂b₂.symm, h.na₁a₂⟩
  · exact ⟨h.b₁'b₂'.symm, h.a₁'b₂'.symm, ha₂'b₂'.symm, h.a₁'b₁'.symm, h.a₂'b₁'.symm,
      h.na₁'a₂'⟩
  · exact ⟨h.b₁b₂', h.b₁'b₂.symm, h.a₁a₁', h.a₂a₂'⟩
  · exact ⟨h.nb₁b₁', h.nb₁a₁', h.nb₁a₂', h.nb₂b₂', h.nb₂a₁',
      fun hc => hna₂'b₂ hc.symm, h.na₁b₂', h.na₁b₁', h.na₁a₂',
      hna₂b₂', h.na₂b₁', fun hc => h.na₁'a₂ hc.symm⟩

set_option maxHeartbeats 1600000 in
/-- **The second pairing.**  `a₂b₂'` and `a₂'b₂` are the two edges of the matching.  The eight
vertices are then the eight edges of `K₃,₃ \\ e`, adjacent exactly when the corresponding edges
share an end, under the labelling

```
x0y0 = b₁    x0y1 = b₂     x0y2 = a₁
x1y0 = b₂'   x1y1 = b₁'    x1y2 = a₁'
x2y0 = a₂    x2y1 = a₂'          (x2y2 is the deleted edge e)
```

so `G ∉ F₃`, and in particular `G ∉ F₆`. -/
theorem not_inF3_of_pairing_two {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {b₁ b₁' a₁ a₁' a₂ a₂' b₂ b₂' : V}
    (h : Config G b₁ b₁' a₁ a₁' a₂ a₂' b₂ b₂')
    (ha₂b₂' : G.Adj a₂ b₂') (ha₂'b₂ : G.Adj a₂' b₂)
    (hna₂b₂ : ¬ G.Adj a₂ b₂) (hna₂'b₂' : ¬ G.Adj a₂' b₂') :
    ¬ InF3 G := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18,
    d19, d20, d21, d22, d23, d24, d25, d26, d27, d28⟩ := config_ne h
  -- both orientations of every disequality, so that `assumption` closes each case
  have s1 := d1.symm; have s2 := d2.symm; have s3 := d3.symm; have s4 := d4.symm
  have s5 := d5.symm; have s6 := d6.symm; have s7 := d7.symm; have s8 := d8.symm
  have s9 := d9.symm; have s10 := d10.symm; have s11 := d11.symm; have s12 := d12.symm
  have s13 := d13.symm; have s14 := d14.symm; have s15 := d15.symm; have s16 := d16.symm
  have s17 := d17.symm; have s18 := d18.symm; have s19 := d19.symm; have s20 := d20.symm
  have s21 := d21.symm; have s22 := d22.symm; have s23 := d23.symm; have s24 := d24.symm
  have s25 := d25.symm; have s26 := d26.symm; have s27 := d27.symm; have s28 := d28.symm
  -- both orientations of every adjacency and non-adjacency
  have p1 := h.a₁a₁'; have p1' := h.a₁a₁'.symm
  have p2 := h.a₂a₂'; have p2' := h.a₂a₂'.symm
  have p3 := h.b₁b₂; have p3' := h.b₁b₂.symm
  have p4 := h.b₁b₂'; have p4' := h.b₁b₂'.symm
  have p5 := h.b₁'b₂; have p5' := h.b₁'b₂.symm
  have p6 := h.b₁'b₂'; have p6' := h.b₁'b₂'.symm
  have p7 := h.b₁a₁; have p7' := h.b₁a₁.symm
  have p8 := h.a₁'b₁'; have p8' := h.a₁'b₁'.symm
  have p9 := h.b₁a₂; have p9' := h.b₁a₂.symm
  have p10 := h.a₂'b₁'; have p10' := h.a₂'b₁'.symm
  have p11 := h.b₂a₁; have p11' := h.b₂a₁.symm
  have p12 := h.a₁'b₂'; have p12' := h.a₁'b₂'.symm
  have p13 := ha₂b₂'; have p13' := ha₂b₂'.symm
  have p14 := ha₂'b₂; have p14' := ha₂'b₂.symm
  have q1 := h.nb₁b₁'; have q1' : ¬ G.Adj b₁' b₁ := fun hc => h.nb₁b₁' hc.symm
  have q2 := h.nb₂b₂'; have q2' : ¬ G.Adj b₂' b₂ := fun hc => h.nb₂b₂' hc.symm
  have q3 := h.nb₁a₁'; have q3' : ¬ G.Adj a₁' b₁ := fun hc => h.nb₁a₁' hc.symm
  have q4 := h.na₁b₁'; have q4' : ¬ G.Adj b₁' a₁ := fun hc => h.na₁b₁' hc.symm
  have q5 := h.nb₁a₂'; have q5' : ¬ G.Adj a₂' b₁ := fun hc => h.nb₁a₂' hc.symm
  have q6 := h.na₂b₁'; have q6' : ¬ G.Adj b₁' a₂ := fun hc => h.na₂b₁' hc.symm
  have q7 := h.nb₂a₁'; have q7' : ¬ G.Adj a₁' b₂ := fun hc => h.nb₂a₁' hc.symm
  have q8 := h.na₁b₂'; have q8' : ¬ G.Adj b₂' a₁ := fun hc => h.na₁b₂' hc.symm
  have q9 := h.na₁a₂; have q9' : ¬ G.Adj a₂ a₁ := fun hc => h.na₁a₂ hc.symm
  have q10 := h.na₁a₂'; have q10' : ¬ G.Adj a₂' a₁ := fun hc => h.na₁a₂' hc.symm
  have q11 := h.na₁'a₂; have q11' : ¬ G.Adj a₂ a₁' := fun hc => h.na₁'a₂ hc.symm
  have q12 := h.na₁'a₂'; have q12' : ¬ G.Adj a₂' a₁' := fun hc => h.na₁'a₂' hc.symm
  have q13 := hna₂b₂; have q13' : ¬ G.Adj b₂ a₂ := fun hc => hna₂b₂ hc.symm
  have q14 := hna₂'b₂'; have q14' : ¬ G.Adj b₂' a₂' := fun hc => hna₂'b₂' hc.symm
  refine Workspace.ProofLemmas.LK33eAppearance.not_inF3_of_LK33e
    (fun p => (![![b₁, b₂, a₁], ![b₂', b₁', a₁'], ![a₂, a₂', b₁]] : Fin 3 → Fin 3 → V)
      p.1 p.2) ?_ ?_ <;>
  · rintro ⟨p1, p2⟩ ⟨q1, q2⟩ hp hq hpq
    fin_cases p1 <;> fin_cases p2 <;> fin_cases q1 <;> fin_cases q2 <;>
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, ne_eq, Prod.mk.injEq, not_and, reduceCtorEq,
        Fin.reduceEq, and_self, not_true_eq_false, and_false, false_and, or_false, or_true,
        true_or, false_or, iff_true, iff_false, not_false_eq_true, forall_const] at hp hq hpq ⊢ <;>
      first
        | assumption
        | exact absurd rfl hp
        | exact absurd rfl hq
        | simp_all

end Workspace.ProofLemmas.Thm151Pairing
