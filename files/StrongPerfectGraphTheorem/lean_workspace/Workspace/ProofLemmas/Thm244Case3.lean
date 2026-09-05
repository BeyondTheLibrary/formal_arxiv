import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.Types.Wheels
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.HoleArc
import Workspace.ProofLemmas.HoleYEdgeParity
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.Thm244Shapes
import Workspace.ProofLemmas.Thm244Parity
import Workspace.Statements.S02.Thm_2_3
import Workspace.Statements.S24.Thm_24_2

/-!
# The third case of the printed proof of 24.4

Chudnovsky–Robertson–Seymour–Thomas, *The Strong Perfect Graph Theorem*, printed p. 144:

> Now suppose the third holds, and let `v₁,v₂,P` be as in the third case.  Let `P` have
> vertices `p₁,…,pₙ` where `v₁ = p₁` and `v₂ = pₙ`.  Since one of its vertices is
> `X₃`-complete and `p₁,pₙ` are not, it follows that `n ≥ 3`; and by (1), `n` is **even**,
> so `n ≥ 4`.  Choose `i` minimum and `j` maximum with `1 ≤ i,j ≤ n` such that `pᵢ,pⱼ` are
> `X₃`-complete.  So `i > 1`, and `i` is even by (1), and similarly `j < n` and `j` is odd.
> So the path `pᵢ-⋯-pⱼ` has odd length, and so by 24.2 one of its edges is `X₃`-complete,
> say `p_k p_{k+1}` where `2 ≤ k ≤ n-2`.  Now `p_k,p_{k+1}` are joined by an antipath with
> interior in `X₁`, and by another with interior in `X₂`, and the union of these is an
> antihole; so they both have length 2.  Hence for `i = 1,2` there exist `xᵢ ∈ Xᵢ`
> nonadjacent to both `p_k,p_{k+1}`.  Let `R` be a path between `p_{k+2},p_{k-1}` with
> interior in `(V(P)\{p_k,p_{k+1}}) ∪ {x₁,x₂}`.  Then `R` can be completed to a hole `C` via
> `p_{k-1}-p_k-p_{k+1}-p_{k+2}`, and `C` has length `≥ 6`, and at least one edge of `C` is
> `X₃`-complete, namely `p_k p_{k+1}`, and at least one more vertex of it is `X₃`-complete,
> since `R` uses at least one of `x₁,x₂`.  But this contradicts 2.3, and the hypothesis that
> `G ∈ F₁₁`.

## Erratum in the printed text

The printed sentence reads *"and by (1), `n` is **odd**, so `n ≥ 4`"*, in both the published
PDF and the arXiv source.  That is a slip.  Claim (1) — proved here as
`Thm244Parity.even_length_of_unique_ends` — concludes that `n` is **even**; and "odd together
with `n ≥ 3`" would give `n ≥ 5`, not the printed `n ≥ 4`, whereas "even together with
`n ≥ 3`" gives exactly `n ≥ 4`.  The remainder of the paragraph (`i` even, `j` odd, hence
`pᵢ-⋯-pⱼ` of odd length) is consistent only with the reading "even", which is what is used
below.  Recorded as `AMBIGUITIES.md` A29.

## Index convention

The paper is 1-indexed; the Lean lists are 0-indexed.  So the paper's `pₜ` is `P[t-1]`, the
paper's `n` is `P.length`, the paper's *"`i` is even"* is *"`t₀` is odd"*, its *"`j` is odd"*
is *"`t₁` is even"*, and its *"`2 ≤ k ≤ n-2`"* is *"`1 ≤ κ` and `κ+3 ≤ P.length`"*.

## Closing sentence

*"But this contradicts 2.3, and the hypothesis that `G ∈ F₁₁`"* is spelled out as follows.
2.3 offers *"an even number of `X₃`-complete edges of `C`, or exactly two `X₃`-complete
vertices of `C` and they are adjacent"*.  The second is refuted by the three distinct
`X₃`-complete vertices `p_k, p_{k+1}` and whichever of `x₁, x₂` the path `R` uses (each `xᵢ`
lies in `Xᵢ`, which is complete to `X₃`).  So the number of `X₃`-complete edges is even, and
it is nonzero, hence `≥ 2`; a second `X₃`-complete edge either is disjoint from
`p_k p_{k+1}` — giving a **wheel** `(C, X₃)`, contrary to `G ∈ F₉` — or meets it, forcing
three cyclically consecutive `X₃`-complete vertices of `C`, so that any vertex of `X₃` has
three consecutive neighbours on a hole of length `≥ 6`, contrary to `G ∈ F₁₀`.  Both `F₉` and
`F₁₀` are contained in the printed hypothesis `G ∈ F₁₁`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Workspace.Types.Thm244Case3

open Workspace.ProofLemmas
open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm244Shapes

variable {V : Type*}

/-! ## Small list utilities -/

/-- Rewriting the *index* of a `getElem` is a motive error; this is the usable form. -/
private theorem gidx {W : Type*} (q : List W) {a b : ℕ} (h : a = b)
    (ha : a < q.length) (hb : b < q.length) : q[a]'ha = q[b]'hb := by
  subst h; rfl

private theorem mem_take_iff {W : Type*} (l : List W) (m : ℕ) (z : W) :
    z ∈ l.take m ↔ ∃ (c : ℕ) (hc : c < l.length), c < m ∧ l[c]'hc = z := by
  constructor
  · intro h
    obtain ⟨c, hc, hcz⟩ := List.getElem_of_mem h
    rw [List.length_take] at hc
    exact ⟨c, by omega, by omega, by rw [← hcz]; simp⟩
  · rintro ⟨c, hc, hcm, hcz⟩
    refine List.mem_iff_getElem.mpr ⟨c, by rw [List.length_take]; omega, ?_⟩
    rw [← hcz]; simp

private theorem mem_drop_iff {W : Type*} (l : List W) (m : ℕ) (z : W) :
    z ∈ l.drop m ↔ ∃ (c : ℕ) (hc : c < l.length), m ≤ c ∧ l[c]'hc = z := by
  constructor
  · intro h
    obtain ⟨c, hc, hcz⟩ := List.getElem_of_mem h
    rw [List.length_drop] at hc
    refine ⟨m + c, by omega, by omega, ?_⟩
    rw [← hcz]; simp
  · rintro ⟨c, hc, hcm, hcz⟩
    refine List.mem_iff_getElem.mpr ⟨c - m, by rw [List.length_drop]; omega, ?_⟩
    rw [← hcz, List.getElem_drop]
    exact gidx l (by omega) (by omega) hc

/-- Every vertex of a path is one of its two ends or an interior vertex. -/
private theorem path_mem_dec {K : SimpleGraph V} {p : List V} {u v : V} {W : Set V}
    (hp : IsPathFrom K p u v) (hint : ∀ z ∈ SPGT.interior p, z ∈ W) :
    ∀ x ∈ p, x = u ∨ x = v ∨ x ∈ W := by
  intro x hx
  obtain ⟨c, hc, hcx⟩ := List.getElem_of_mem hx
  have hpos : 0 < p.length := by omega
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · exact Or.inl (by rw [← hcx]; exact PathBasics.getElem_zero_of_head? hp.2.1 hpos)
  · by_cases hcl : c + 1 = p.length
    · refine Or.inr (Or.inl ?_)
      rw [← hcx, gidx p (show c = p.length - 1 by omega) hc (by omega)]
      exact PathBasics.getElem_last_of_getLast? hp.2.2 hpos
    · exact Or.inr (Or.inr (by
        rw [← hcx]
        exact hint _ (PathBasics.getElem_mem_interior hp.1 hc hc0 (by omega))))

/-! ## *"the union of these is an antihole; so they both have length 2"* -/

/-- The printed step *"`p_k,p_{k+1}` are joined by an antipath with interior in `X₁`, and by
another with interior in `X₂`, and the union of these is an antihole; so they both have
length 2.  Hence there exist `xᵢ ∈ Xᵢ` nonadjacent to both `p_k,p_{k+1}`."*

Stated asymmetrically (it produces the vertex of `Y`); apply it twice, once with `(Y,Z)` and
once with `(Z,Y)`. -/
private theorem antipath_pair [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : InF11 G)
    (Y Z : Set V) (hYZ : Disjoint Y Z)
    (hYa : AnticonnectedSet G Y) (hZa : AnticonnectedSet G Z) (hYZc : Complete G Y Z)
    (s t : V) (hst : G.Adj s t)
    (hsY : s ∉ Y) (htY : t ∉ Y) (hsZ : s ∉ Z) (htZ : t ∉ Z)
    (hsY' : ∃ y ∈ Y, ¬ G.Adj s y) (htY' : ∃ y ∈ Y, ¬ G.Adj t y)
    (hsZ' : ∃ z ∈ Z, ¬ G.Adj s z) (htZ' : ∃ z ∈ Z, ¬ G.Adj t z) :
    ∃ y ∈ Y, ¬ G.Adj s y ∧ ¬ G.Adj t y := by
  obtain ⟨A, hA, hAint⟩ :=
    InducedPathExtraction.exists_antipath_interior_in hYa hsY htY hsY' htY'
  obtain ⟨B, hB, hBint⟩ :=
    InducedPathExtraction.exists_antipath_interior_in hZa hsZ htZ hsZ' htZ'
  have hA' : IsPathFrom Gᶜ A s t := hA
  have hB' : IsPathFrom Gᶜ B s t := hB
  have hnadj : ¬ Gᶜ.Adj s t := by
    rw [SimpleGraph.compl_adj]; push_neg; intro _; exact hst
  have hA3 : 3 ≤ A.length := MinimalConnectedIsPath.three_le_length_of_not_adj hA' hst.ne hnadj
  have hB3 : 3 ≤ B.length := MinimalConnectedIsPath.three_le_length_of_not_adj hB' hst.ne hnadj
  -- `B` reversed, with both ends stripped, is the second half of the cycle
  have hBrev : IsPathFrom Gᶜ B.reverse t s := PathBasics.isPathFrom_reverse hB'
  have hBrevlen : B.reverse.length = B.length := List.length_reverse
  have hBr3 : 3 ≤ B.reverse.length := by omega
  have hE : IsPathFrom Gᶜ (SPGT.interior B.reverse)
      (B.reverse[1]'(by omega)) (B.reverse[B.reverse.length - 2]'(by omega)) :=
    PathGlue.isPathFrom_interior hBrev.1 hBr3
  have hEZ : ∀ z ∈ SPGT.interior B.reverse, z ∈ Z := fun z hz =>
    hBint z (PathBasics.mem_interior_reverse.mp hz)
  have hElen : (SPGT.interior B.reverse).length = B.length - 2 := by
    rw [PathBasics.interior_length]; omega
  have hBrnd : B.reverse.Nodup := PathBasics.path_nodup hBrev.1
  have hBr0 : B.reverse[0]'(by omega) = t :=
    PathBasics.getElem_zero_of_head? hBrev.2.1 (by omega)
  have hBrl : B.reverse[B.reverse.length - 1]'(by omega) = s :=
    PathBasics.getElem_last_of_getLast? hBrev.2.2 (by omega)
  have hAdec : ∀ x ∈ A, x = s ∨ x = t ∨ x ∈ Y := path_mem_dec hA' hAint
  have hdisj : ∀ x ∈ A, x ∉ SPGT.interior B.reverse := by
    intro x hx hxE
    rcases hAdec x hx with h | h | h
    · exact hsZ (h ▸ hEZ x hxE)
    · exact htZ (h ▸ hEZ x hxE)
    · exact (Set.disjoint_left.mp hYZ h) (hEZ x hxE)
  have hcross : ∀ x ∈ A, ∀ y ∈ SPGT.interior B.reverse,
      (Gᶜ.Adj x y ↔ (x = t ∧ y = B.reverse[1]'(by omega)) ∨
        (x = s ∧ y = B.reverse[B.reverse.length - 2]'(by omega))) := by
    intro x hx y hy
    obtain ⟨e, he, he1, he2, hey⟩ := PathBasics.exists_getElem_of_mem_interior hBrev.1 hy
    have eq1 : (B.reverse[e]'he = B.reverse[1]'(by omega)) ↔ e = 1 := hBrnd.getElem_inj_iff
    have eq2 : (B.reverse[e]'he = B.reverse[B.reverse.length - 2]'(by omega)) ↔
        e = B.reverse.length - 2 := hBrnd.getElem_inj_iff
    rcases hAdec x hx with h | h | h
    · subst h
      rw [← hey, eq1, eq2]
      have hadj := PathBasics.path_adj_iff hBrev.1
        (show B.reverse.length - 1 < B.reverse.length by omega) he
      rw [hBrl] at hadj
      rw [hadj]
      constructor
      · intro hh; exact Or.inr ⟨rfl, by omega⟩
      · rintro (⟨hh, -⟩ | ⟨-, hh⟩)
        · exact absurd hh hst.ne
        · omega
    · subst h
      rw [← hey, eq1, eq2]
      have hadj := PathBasics.path_adj_iff hBrev.1
        (show (0 : ℕ) < B.reverse.length by omega) he
      rw [hBr0] at hadj
      rw [hadj]
      constructor
      · intro hh; exact Or.inl ⟨rfl, by omega⟩
      · rintro (⟨-, hh⟩ | ⟨hh, -⟩)
        · omega
        · exact absurd hh.symm hst.ne
    · refine iff_of_false ?_ ?_
      · rw [SimpleGraph.compl_adj]; push_neg; intro _
        exact hYZc x h y (hEZ y hy)
      · rintro (⟨hh, -⟩ | ⟨hh, -⟩)
        · exact htY (hh ▸ h)
        · exact hsY (hh ▸ h)
  have hhole : IsHoleList Gᶜ (A ++ SPGT.interior B.reverse) :=
    PathGlue.glue_hole hA' hE hdisj hcross (by omega)
  have h4 := HoleArc.antihole_length_of_inF11 hG _ hhole
  simp only [holeLength, List.length_append, hElen] at h4
  have hA3' : A.length = 3 := by omega
  -- so `A = [s, y, t]`
  have hy : (A[1]'(by omega)) ∈ Y :=
    hAint _ (PathBasics.getElem_mem_interior hA'.1 (by omega) le_rfl (by omega))
  have hA0 : A[0]'(by omega) = s := PathBasics.getElem_zero_of_head? hA'.2.1 (by omega)
  have hA2 : A[2]'(by omega) = t := by
    have := PathBasics.getElem_last_of_getLast? hA'.2.2 (show 0 < A.length by omega)
    rwa [gidx A (show A.length - 1 = 2 by omega) (by omega) (by omega)] at this
  refine ⟨A[1]'(by omega), hy, ?_, ?_⟩
  · have hadj := PathBasics.path_adj_succ hA'.1 (show 0 + 1 < A.length by omega)
    rw [hA0] at hadj
    rw [SimpleGraph.compl_adj] at hadj
    exact hadj.2
  · have hadj := PathBasics.path_adj_succ hA'.1 (show 1 + 1 < A.length by omega)
    have h12 : A[1 + 1]'(by omega) = A[2]'(by omega) := gidx A (by omega) (by omega) (by omega)
    rw [h12, hA2] at hadj
    rw [SimpleGraph.compl_adj] at hadj
    exact fun hcon => hadj.2 hcon.symm

/-! ## *"contradicts 2.3"*: a second `Y`-complete edge -/

/-- If a hole `C` disjoint from an anticonnected `Y` has three distinct `Y`-complete
vertices and at least one `Y`-complete edge, then it has a **second** `Y`-complete edge:
2.3's first alternative (an even number of `Y`-complete edges) must hold, since its second
alternative allows only two `Y`-complete vertices. -/
private theorem second_yEdge [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hBerge : Berge G)
    {Y : Set V} (hY : AnticonnectedSet G Y) {C : List V} (hC : IsHoleList G C)
    (hCY : ∀ w ∈ C, w ∉ Y)
    {c₁ c₂ c₃ : V} (h1 : c₁ ∈ C) (h2 : c₂ ∈ C) (h3 : c₃ ∈ C)
    (hd12 : c₁ ≠ c₂) (hd13 : c₁ ≠ c₃) (hd23 : c₂ ≠ c₃)
    (hy1 : VertexComplete G c₁ Y) (hy2 : VertexComplete G c₂ Y) (hy3 : VertexComplete G c₃ Y)
    {e₀ : Sym2 V} (he₀ : e₀ ∈ HoleYEdgeParity.yEdges G Y C) :
    ∃ e ∈ HoleYEdgeParity.yEdges G Y C, e ≠ e₀ := by
  have h23 := (_root_.Workspace.Statements.S02.SPGT.thm_2_3 G hBerge Y hY C (Or.inr hC) hCY).2 hC
  rcases h23 with heven | ⟨α, β, hset, -, -⟩
  · have heven' : Even (HoleYEdgeParity.yEdges G Y C).ncard := heven
    have hpos : 0 < (HoleYEdgeParity.yEdges G Y C).ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨e₀, he₀⟩
    have h1lt : 1 < (HoleYEdgeParity.yEdges G Y C).ncard := by
      rw [Nat.even_iff] at heven'; omega
    exact Set.exists_ne_of_one_lt_ncard h1lt e₀
  · exfalso
    have m1 : c₁ ∈ ({α, β} : Set V) := by rw [← hset]; exact ⟨h1, hy1⟩
    have m2 : c₂ ∈ ({α, β} : Set V) := by rw [← hset]; exact ⟨h2, hy2⟩
    have m3 : c₃ ∈ ({α, β} : Set V) := by rw [← hset]; exact ⟨h3, hy3⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at m1 m2 m3
    rcases m1 with q1 | q1 <;> rcases m2 with q2 | q2 <;> rcases m3 with q3 | q3 <;>
      simp_all

/-- The `F₁₀` clause of `InF11`, in the shape a caller with three *listed* consecutive
vertices can use: no vertex of `Y` may be adjacent to three consecutive vertices of a hole of
length `≥ 6`, so a hole cannot carry three consecutive `Y`-complete vertices. -/
private theorem three_consecutive_absurd [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : InF11 G) {Y : Set V} (hYne : Y.Nonempty) {C : List V} (hC : IsHoleList G C)
    (hC6 : 6 ≤ holeLength C) {c₀ c₁ c₂ : V} (hpre : [c₀, c₁, c₂] <+: C)
    (h0 : VertexComplete G c₀ Y) (h1 : VertexComplete G c₁ Y) (h2 : VertexComplete G c₂ Y) :
    False := by
  obtain ⟨y, hy⟩ := hYne
  exact HoleArc.noThreeConsecutive_of_inF11 hG C hC hC6
    ⟨y, c₀, c₁, c₂, ⟨0, by rw [List.rotate_zero]; exact hpre⟩,
      (h0 y hy).symm, (h1 y hy).symm, (h2 y hy).symm⟩

/-! ## The refutation -/

/-- **Case 3 of the printed proof of 24.4 is impossible.** -/
theorem case3_refute [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : InF11 G)
    (X : Fin 3 → Set V)
    (hXdisj : ∀ l₁ l₂ : Fin 3, l₁ ≠ l₂ → Disjoint (X l₁) (X l₂))
    (hXne : ∀ l : Fin 3, (X l).Nonempty)
    (hXanti : ∀ l : Fin 3, AnticonnectedSet G (X l))
    (hXcomp : ∀ l₁ l₂ : Fin 3, l₁ ≠ l₂ → Complete G (X l₁) (X l₂))
    (F : Set V) (hFX : ∀ w ∈ F, ∀ l : Fin 3, w ∉ X l)
    (hno : ∀ w ∈ F, ∀ l₁ l₂ : Fin 3, l₁ ≠ l₂ →
      ¬ (VertexComplete G w (X l₁) ∧ VertexComplete G w (X l₂)))
    (i j k : Fin 3) (P : List V) (a b : V)
    (hshape : ThroughPath G F (fun l => {w : V | VertexComplete G w (X l)}) i j k P a b) :
    False := by
  classical
  obtain ⟨hij, hik, hjk, hP, hPF, haNi, hbNj, hauniq, hbuniq, hwex⟩ := hshape
  simp only [Set.mem_setOf_eq] at haNi hbNj hauniq hbuniq hwex
  have hBerge : Berge G := HoleArc.berge_of_inF11 hG
  have hnd : P.Nodup := PathBasics.path_nodup hP.1
  have hpos : 0 < P.length := PathBasics.path_length_pos hP.1
  have hP0 : P[0]'hpos = a := PathBasics.getElem_zero_of_head? hP.2.1 hpos
  have hPl : P[P.length - 1]'(by omega) = b :=
    PathBasics.getElem_last_of_getLast? hP.2.2 hpos
  have haF : a ∈ F := hPF a (PathBasics.head_mem hP.2.1)
  have hbF : b ∈ F := hPF b (PathBasics.getLast_mem hP.2.2)
  have hab : a ≠ b := by
    intro h
    exact hno a haF i j hij ⟨haNi, by rw [h]; exact hbNj⟩
  have hn2 : 2 ≤ P.length := by
    by_contra hc
    exact hab (by rw [← hP0, ← hPl]; exact gidx P (by omega) hpos (by omega))
  have hank : ¬ VertexComplete G a (X k) := fun h => hno a haF i k hik ⟨haNi, h⟩
  have hbnk : ¬ VertexComplete G b (X k) := fun h => hno b hbF j k hjk ⟨hbNj, h⟩
  -- the two uniqueness clauses, transported from `F` to `P`
  have hPuI : ∀ z ∈ P, (VertexComplete G z (X i) ↔ z = a) := fun z hz =>
    ⟨fun h => hauniq z (hPF z hz) h, fun h => by rw [h]; exact haNi⟩
  have hPuJ : ∀ z ∈ P, (VertexComplete G z (X j) ↔ z = b) := fun z hz =>
    ⟨fun h => hbuniq z (hPF z hz) h, fun h => by rw [h]; exact hbNj⟩
  -- the `X k`-complete positions of `P`
  set Comp : ℕ → Prop := fun t => ∃ (h : t < P.length), VertexComplete G (P[t]'h) (X k)
    with hCompdef
  have hex : ∃ t, Comp t := by
    obtain ⟨w, hwP, hwk⟩ := hwex
    obtain ⟨c, hc, hcw⟩ := List.getElem_of_mem hwP
    exact ⟨c, hc, by rw [hcw]; exact hwk⟩
  obtain ⟨ht₀lt, ht₀c⟩ : Comp (Nat.find hex) := Nat.find_spec hex
  set t₀ := Nat.find hex with ht₀def
  have ht₀min : ∀ m, Comp m → t₀ ≤ m := fun m hm => Nat.find_le hm
  have ht₁ : Comp (Nat.findGreatest Comp (P.length - 1)) := by
    obtain ⟨m, hm⟩ := hex
    exact Nat.findGreatest_spec (m := m) (by obtain ⟨h, -⟩ := hm; omega) hm
  set t₁ := Nat.findGreatest Comp (P.length - 1) with ht₁def
  obtain ⟨ht₁lt, ht₁c⟩ := ht₁
  have ht₁max : ∀ m, t₁ < m → m ≤ P.length - 1 → ¬ Comp m := fun m h1 h2 =>
    Nat.findGreatest_is_greatest h1 h2
  have ht₀pos : 0 < t₀ := by
    rcases Nat.eq_zero_or_pos t₀ with h | h
    · have ht₀eq : P[t₀]'ht₀lt = a := by
        rw [gidx P h ht₀lt hpos, hP0]
      rw [ht₀eq] at ht₀c
      exact absurd ht₀c hank
    · exact h
  have ht₁lt' : t₁ < P.length - 1 := by
    rcases (show t₁ = P.length - 1 ∨ t₁ < P.length - 1 by
      have := Nat.findGreatest_le (P.length - 1) (P := Comp); omega) with h | h
    · exact absurd (by rw [← hPl, ← gidx P h (by omega) (by omega)]; exact ht₁c) hbnk
    · exact h
  have ht₀le : t₀ ≤ t₁ := ht₀min t₁ ⟨ht₁lt, ht₁c⟩
  have hn3 : 3 ≤ P.length := by omega
  -- *"by (1), `n` is even, so `n ≥ 4`"*
  have hEvenN : Even P.length :=
    Thm244Parity.even_length_of_unique_ends G hG (X i) (X j) (hXdisj i j hij) (hXne i)
      (hXne j) (hXanti i) (hXanti j) (hXcomp i j hij) P a b hP.1 hP.2.1 hP.2.2 hab hPuI hPuJ
  -- *"`i` is even by (1)"* — 0-indexed, `t₀` is odd
  have hEven₀ : Even (t₀ + 1) := by
    have hsl : IsPathFrom G ((P.drop 0).take (t₀ - 0 + 1)) (P[0]'(by omega)) (P[t₀]'ht₀lt) :=
      PathBasics.isPathFrom_slice hP.1 ht₀pos ht₀lt
    have hmem (z : V) :=
      PathBasics.mem_slice_iff P (i := 0) (j := t₀) (x := z) (by omega) ht₀lt
    have hsub : ∀ z ∈ (P.drop 0).take (t₀ - 0 + 1), z ∈ P := by
      intro z hz
      obtain ⟨c, hc, -, -, hcz⟩ := (hmem z).mp hz
      rw [← hcz]; exact List.getElem_mem hc
    have huI : ∀ z ∈ (P.drop 0).take (t₀ - 0 + 1),
        (VertexComplete G z (X i) ↔ z = P[0]'(by omega)) := by
      intro z hz
      rw [hP0]
      exact hPuI z (hsub z hz)
    have huK : ∀ z ∈ (P.drop 0).take (t₀ - 0 + 1),
        (VertexComplete G z (X k) ↔ z = P[t₀]'ht₀lt) := by
      intro z hz
      obtain ⟨c, hc, -, hct, hcz⟩ := (hmem z).mp hz
      constructor
      · intro hzk
        have : Comp c := ⟨hc, by rw [hcz]; exact hzk⟩
        have := ht₀min c this
        rw [← hcz]
        exact gidx P (by omega) hc ht₀lt
      · intro hze
        rw [hze]; exact ht₀c
    have hne : (P[0]'(by omega)) ≠ (P[t₀]'ht₀lt) :=
      PathBasics.path_ne_of_ne_index hP.1 (by omega) ht₀lt (by omega)
    have := Thm244Parity.even_length_of_unique_ends G hG (X i) (X k) (hXdisj i k hik)
      (hXne i) (hXne k) (hXanti i) (hXanti k) (hXcomp i k hik)
      ((P.drop 0).take (t₀ - 0 + 1)) (P[0]'(by omega)) (P[t₀]'ht₀lt)
      hsl.1 hsl.2.1 hsl.2.2 hne huI huK
    rwa [PathBasics.length_slice P (by omega) ht₀lt, show t₀ - 0 + 1 = t₀ + 1 by omega] at this
  -- *"`j` is odd"* — 0-indexed, `t₁` is even
  have hEven₁ : Even (P.length - 1 - t₁ + 1) := by
    have hsl : IsPathFrom G ((P.drop t₁).take (P.length - 1 - t₁ + 1)) (P[t₁]'ht₁lt)
        (P[P.length - 1]'(by omega)) :=
      PathBasics.isPathFrom_slice hP.1 (by omega) (by omega)
    have hmem (z : V) := PathBasics.mem_slice_iff P (i := t₁) (j := P.length - 1)
      (x := z) (by omega) (by omega)
    have hsub : ∀ z ∈ (P.drop t₁).take (P.length - 1 - t₁ + 1), z ∈ P := by
      intro z hz
      obtain ⟨c, hc, -, -, hcz⟩ := (hmem z).mp hz
      rw [← hcz]; exact List.getElem_mem hc
    have huK : ∀ z ∈ (P.drop t₁).take (P.length - 1 - t₁ + 1),
        (VertexComplete G z (X k) ↔ z = P[t₁]'ht₁lt) := by
      intro z hz
      obtain ⟨c, hc, hct, -, hcz⟩ := (hmem z).mp hz
      constructor
      · intro hzk
        have hcomp : Comp c := ⟨hc, by rw [hcz]; exact hzk⟩
        have hle : c ≤ t₁ := by
          by_contra hcon
          exact ht₁max c (by omega) (by omega) hcomp
        rw [← hcz]
        exact gidx P (by omega) hc ht₁lt
      · intro hze
        rw [hze]; exact ht₁c
    have huJ : ∀ z ∈ (P.drop t₁).take (P.length - 1 - t₁ + 1),
        (VertexComplete G z (X j) ↔ z = P[P.length - 1]'(by omega)) := by
      intro z hz
      rw [hPl]
      exact hPuJ z (hsub z hz)
    have hne : (P[t₁]'ht₁lt) ≠ (P[P.length - 1]'(by omega)) :=
      PathBasics.path_ne_of_ne_index hP.1 ht₁lt (by omega) (by omega)
    have := Thm244Parity.even_length_of_unique_ends G hG (X k) (X j) (hXdisj k j (Ne.symm hjk))
      (hXne k) (hXne j) (hXanti k) (hXanti j) (hXcomp k j (Ne.symm hjk))
      ((P.drop t₁).take (P.length - 1 - t₁ + 1)) (P[t₁]'ht₁lt) (P[P.length - 1]'(by omega))
      hsl.1 hsl.2.1 hsl.2.2 hne huK huJ
    rwa [PathBasics.length_slice P (by omega) (show P.length - 1 < P.length by omega)] at this
  -- arithmetic: `t₀` odd, `t₁` even, so `t₁ - t₀` is odd
  have hparity : t₀ % 2 = 1 ∧ t₁ % 2 = 0 := by
    rw [Nat.even_iff] at hEvenN hEven₀ hEven₁
    omega
  have ht₀lt₁ : t₀ < t₁ := by omega
  -- *"by 24.2 one of its edges is `X₃`-complete"*
  have hslK : IsPathFrom G ((P.drop t₀).take (t₁ - t₀ + 1)) (P[t₀]'ht₀lt) (P[t₁]'ht₁lt) :=
    PathBasics.isPathFrom_slice hP.1 ht₀lt₁ ht₁lt
  have hoddK : Odd (pathLength ((P.drop t₀).take (t₁ - t₀ + 1))) := by
    rw [PathBasics.pathLength_eq, PathBasics.length_slice P (le_of_lt ht₀lt₁) ht₁lt,
      Nat.odd_iff]
    omega
  obtain ⟨α, hαm, β, hβm, hEC⟩ :=
    _root_.Workspace.Statements.S24.SPGT.thm_24_2 G hG _ _ _ hslK hoddK (X k) (hXanti k)
      ht₀c ht₁c
  have hmemK (z : V) := PathBasics.mem_slice_iff P (i := t₀) (j := t₁) (x := z)
    (le_of_lt ht₀lt₁) ht₁lt
  obtain ⟨sα, hsα, hsα1, hsα2, hsαe⟩ := (hmemK α).mp hαm
  obtain ⟨sβ, hsβ, hsβ1, hsβ2, hsβe⟩ := (hmemK β).mp hβm
  have hadjαβ : G.Adj (P[sα]'hsα) (P[sβ]'hsβ) := by rw [hsαe, hsβe]; exact hEC.1
  have hindex : sα + 1 = sβ ∨ sβ + 1 = sα :=
    (PathBasics.path_adj_iff hP.1 hsα hsβ).mp hadjαβ
  -- the index `κ` of the printed `p_k`
  obtain ⟨κ, hκ1, hκ2, hκA, hκB⟩ :
      ∃ κ : ℕ, 1 ≤ κ ∧ κ + 3 ≤ P.length ∧
        (∃ (h : κ < P.length), VertexComplete G (P[κ]'h) (X k)) ∧
        (∃ (h : κ + 1 < P.length), VertexComplete G (P[κ + 1]'h) (X k)) := by
    rcases hindex with h | h
    · refine ⟨sα, by omega, by omega, ⟨hsα, ?_⟩, ⟨by omega, ?_⟩⟩
      · rw [hsαe]; exact hEC.2.1
      · rw [gidx P h (by omega) hsβ, hsβe]; exact hEC.2.2
    · refine ⟨sβ, by omega, by omega, ⟨hsβ, ?_⟩, ⟨by omega, ?_⟩⟩
      · rw [hsβe]; exact hEC.2.2
      · rw [gidx P h (by omega) hsα, hsαe]; exact hEC.2.1
  obtain ⟨hκlt, hκk⟩ := hκA
  obtain ⟨hκ1lt, hκ1k⟩ := hκB
  have hκadj : G.Adj (P[κ]'hκlt) (P[κ + 1]'hκ1lt) := PathBasics.path_adj_succ hP.1 hκ1lt
  have hκF : (P[κ]'hκlt) ∈ F := hPF _ (List.getElem_mem hκlt)
  have hκ1F : (P[κ + 1]'hκ1lt) ∈ F := hPF _ (List.getElem_mem hκ1lt)
  -- neither of the two is `X i`- or `X j`-complete
  have hnc : ∀ (w : V), w ∈ F → VertexComplete G w (X k) → ∀ l : Fin 3, l ≠ k →
      ∃ x ∈ X l, ¬ G.Adj w x := by
    intro w hwF hwk l hlk
    have : ¬ VertexComplete G w (X l) := fun h => hno w hwF l k hlk ⟨h, hwk⟩
    simpa [VertexComplete] using this
  obtain ⟨x₁, hx₁X, hx₁a, hx₁b⟩ :=
    antipath_pair G hG (X i) (X j) (hXdisj i j hij) (hXanti i) (hXanti j) (hXcomp i j hij)
      _ _ hκadj (hFX _ hκF i) (hFX _ hκ1F i) (hFX _ hκF j) (hFX _ hκ1F j)
      (hnc _ hκF hκk i hik) (hnc _ hκ1F hκ1k i hik)
      (hnc _ hκF hκk j hjk) (hnc _ hκ1F hκ1k j hjk)
  obtain ⟨x₂, hx₂X, hx₂a, hx₂b⟩ :=
    antipath_pair G hG (X j) (X i) (hXdisj j i (Ne.symm hij)) (hXanti j) (hXanti i)
      (hXcomp j i (Ne.symm hij))
      _ _ hκadj (hFX _ hκF j) (hFX _ hκ1F j) (hFX _ hκF i) (hFX _ hκ1F i)
      (hnc _ hκF hκk j hjk) (hnc _ hκ1F hκ1k j hjk)
      (hnc _ hκF hκk i hik) (hnc _ hκ1F hκ1k i hik)
  -- *"Let `R` be a path between `p_{k+2}, p_{k-1}` with interior in `(V(P)\{p_k,p_{k+1}}) ∪ {x₁,x₂}`"*
  have hLconn : ConnectedSet G {z : V | z ∈ P.take κ} :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (PathBasics.isPathList_take hP.1 (by omega))
  have hRconn : ConnectedSet G {z : V | z ∈ P.drop (κ + 2)} :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (PathBasics.isPathList_drop hP.1 (by omega))
  have haL : a ∈ {z : V | z ∈ P.take κ} := (mem_take_iff P κ a).mpr ⟨0, hpos, by omega, hP0⟩
  have hbR : b ∈ {z : V | z ∈ P.drop (κ + 2)} :=
    (mem_drop_iff P (κ + 2) b).mpr ⟨P.length - 1, by omega, by omega, hPl⟩
  have hax₁ : G.Adj a x₁ := haNi x₁ hx₁X
  have hbx₂ : G.Adj b x₂ := hbNj x₂ hx₂X
  have hx₁x₂ : G.Adj x₁ x₂ := hXcomp i j hij x₁ hx₁X x₂ hx₂X
  have hC1 : ConnectedSet G ({z : V | z ∈ P.take κ} ∪ {x₁}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hLconn ⟨a, haL, hax₁.symm⟩
  have hC2 : ConnectedSet G (({z : V | z ∈ P.take κ} ∪ {x₁}) ∪ {x₂}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hC1 ⟨x₁, Or.inr rfl, hx₁x₂.symm⟩
  have hSconn : ConnectedSet G ((({z : V | z ∈ P.take κ} ∪ {x₁}) ∪ {x₂}) ∪
      {z : V | z ∈ P.drop (κ + 2)}) :=
    ConnectedSetUnionAttach.connectedSet_union hC2 hRconn
      (Or.inr ⟨x₂, Or.inr rfl, b, hbR, hbx₂.symm⟩)
  have hmemL : (P[κ - 1]'(by omega)) ∈ ((({z : V | z ∈ P.take κ} ∪ {x₁}) ∪ {x₂}) ∪
      {z : V | z ∈ P.drop (κ + 2)}) :=
    Or.inl (Or.inl (Or.inl ((mem_take_iff P κ _).mpr ⟨κ - 1, by omega, by omega, rfl⟩)))
  have hmemR : (P[κ + 2]'(by omega)) ∈ ((({z : V | z ∈ P.take κ} ∪ {x₁}) ∪ {x₂}) ∪
      {z : V | z ∈ P.drop (κ + 2)}) :=
    Or.inr ((mem_drop_iff P (κ + 2) _).mpr ⟨κ + 2, by omega, by omega, rfl⟩)
  obtain ⟨R, hR, hRS⟩ :=
    InducedPathExtraction.exists_isPathFrom_of_connected hSconn hmemR hmemL
  have hSdec : ∀ z ∈ ((({z : V | z ∈ P.take κ} ∪ {x₁}) ∪ {x₂}) ∪
      {z : V | z ∈ P.drop (κ + 2)}),
      (∃ (c : ℕ) (hc : c < P.length), c < κ ∧ P[c]'hc = z) ∨ z = x₁ ∨ z = x₂ ∨
      (∃ (c : ℕ) (hc : c < P.length), κ + 2 ≤ c ∧ P[c]'hc = z) := by
    rintro z (((hz | hz) | hz) | hz)
    · exact Or.inl ((mem_take_iff P κ z).mp hz)
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr (Or.inl hz))
    · exact Or.inr (Or.inr (Or.inr ((mem_drop_iff P (κ + 2) z).mp hz)))
  have hRdec : ∀ z ∈ R,
      (∃ (c : ℕ) (hc : c < P.length), c < κ ∧ P[c]'hc = z) ∨ z = x₁ ∨ z = x₂ ∨
      (∃ (c : ℕ) (hc : c < P.length), κ + 2 ≤ c ∧ P[c]'hc = z) := fun z hz =>
    hSdec z (hRS z hz)
  have hRnd : R.Nodup := PathBasics.path_nodup hR.1
  have hRpos : 0 < R.length := PathBasics.path_length_pos hR.1
  have hR0 : R[0]'hRpos = P[κ + 2]'(by omega) :=
    PathBasics.getElem_zero_of_head? hR.2.1 hRpos
  have hRlst : R[R.length - 1]'(by omega) = P[κ - 1]'(by omega) :=
    PathBasics.getElem_last_of_getLast? hR.2.2 hRpos
  -- `x₁`, `x₂` lie outside `P`
  have hx₁P : x₁ ∉ P := fun h => hFX _ (hPF _ h) i hx₁X
  have hx₂P : x₂ ∉ P := fun h => hFX _ (hPF _ h) j hx₂X
  -- *"`R` uses at least one of `x₁, x₂`"*
  have hRuses : x₁ ∈ R ∨ x₂ ∈ R := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨hn1, hn2⟩ := hcon
    have hdecR : ∀ (m : ℕ) (hm : m < R.length),
        (∃ (c : ℕ) (hc : c < P.length), c < κ ∧ P[c]'hc = R[m]'hm) ∨
        (∃ (c : ℕ) (hc : c < P.length), κ + 2 ≤ c ∧ P[c]'hc = R[m]'hm) := by
      intro m hm
      rcases hRdec _ (List.getElem_mem hm) with h | h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ List.getElem_mem hm) hn1
      · exact absurd (h ▸ List.getElem_mem hm) hn2
      · exact Or.inr h
    have hLex : ∃ m, ∃ (hm : m < R.length),
        ∃ (c : ℕ) (hc : c < P.length), c < κ ∧ P[c]'hc = R[m]'hm := by
      refine ⟨R.length - 1, by omega, κ - 1, by omega, by omega, ?_⟩
      rw [hRlst]
    classical
    set LeftAt : ℕ → Prop := fun m => ∃ (hm : m < R.length),
      ∃ (c : ℕ) (hc : c < P.length), c < κ ∧ P[c]'hc = R[m]'hm with hLdef
    have hLex' : ∃ m, LeftAt m := hLex
    obtain ⟨hm₀, c₀, hc₀, hc₀κ, hc₀e⟩ : LeftAt (Nat.find hLex') := Nat.find_spec hLex'
    set m₀ := Nat.find hLex' with hm₀def
    have hm₀min : ∀ m, m < m₀ → ¬ LeftAt m := fun m hm => Nat.find_min hLex' hm
    have hm₀pos : 0 < m₀ := by
      rcases Nat.eq_zero_or_pos m₀ with h | h
      · exfalso
        have hfind : Nat.find hLex' = 0 := by omega
        have hRfind : R[Nat.find hLex']'(by omega) = R[0]'hRpos :=
          gidx R hfind (by omega) hRpos
        rw [hRfind, hR0] at hc₀e
        have := hnd.getElem_inj_iff.mp hc₀e
        omega
      · exact h
    have hprev : m₀ - 1 < R.length := by omega
    rcases hdecR (m₀ - 1) hprev with h | h
    · exact hm₀min (m₀ - 1) (by omega) ⟨hprev, h⟩
    · obtain ⟨c₁, hc₁, hc₁κ, hc₁e⟩ := h
      have hadj : G.Adj (R[m₀ - 1]'hprev) (R[m₀]'hm₀) := by
        have := PathBasics.path_adj_succ hR.1 (show (m₀ - 1) + 1 < R.length by omega)
        rwa [gidx R (show (m₀ - 1) + 1 = m₀ by omega) (by omega) hm₀] at this
      rw [← hc₁e, ← hc₀e] at hadj
      have := (PathBasics.path_adj_iff hP.1 hc₁ hc₀).mp hadj
      omega
  -- *"`R` can be completed to a hole `C` via `p_{k-1}-p_k-p_{k+1}-p_{k+2}`"*
  have hκR : (P[κ]'hκlt) ∉ R := by
    intro h
    rcases hRdec _ h with ⟨c, hc, hcκ, hce⟩ | he | he | ⟨c, hc, hcκ, hce⟩
    · have := hnd.getElem_inj_iff.mp hce; omega
    · exact hx₁P (he ▸ List.getElem_mem hκlt)
    · exact hx₂P (he ▸ List.getElem_mem hκlt)
    · have := hnd.getElem_inj_iff.mp hce; omega
  have hκ1R : (P[κ + 1]'hκ1lt) ∉ R := by
    intro h
    rcases hRdec _ h with ⟨c, hc, hcκ, hce⟩ | he | he | ⟨c, hc, hcκ, hce⟩
    · have := hnd.getElem_inj_iff.mp hce; omega
    · exact hx₁P (he ▸ List.getElem_mem hκ1lt)
    · exact hx₂P (he ▸ List.getElem_mem hκ1lt)
    · have := hnd.getElem_inj_iff.mp hce; omega
  -- inside `S`, the only neighbour of `p_k` is `p_{k-1}` and that of `p_{k+1}` is `p_{k+2}`
  have hκnbr : ∀ z ∈ R, G.Adj (P[κ]'hκlt) z → z = P[κ - 1]'(by omega) := by
    intro z hz hadj
    rcases hRdec z hz with ⟨c, hc, hcκ, hce⟩ | he | he | ⟨c, hc, hcκ, hce⟩
    · rw [← hce] at hadj ⊢
      have := (PathBasics.path_adj_iff hP.1 hκlt hc).mp hadj
      exact gidx P (by omega) hc (by omega)
    · exact absurd (he ▸ hadj) (fun hh => hx₁a hh)
    · exact absurd (he ▸ hadj) (fun hh => hx₂a hh)
    · rw [← hce] at hadj
      have := (PathBasics.path_adj_iff hP.1 hκlt hc).mp hadj
      omega
  have hκ1nbr : ∀ z ∈ R, G.Adj (P[κ + 1]'hκ1lt) z → z = P[κ + 2]'(by omega) := by
    intro z hz hadj
    rcases hRdec z hz with ⟨c, hc, hcκ, hce⟩ | he | he | ⟨c, hc, hcκ, hce⟩
    · rw [← hce] at hadj
      have := (PathBasics.path_adj_iff hP.1 hκ1lt hc).mp hadj
      omega
    · exact absurd (he ▸ hadj) (fun hh => hx₁b hh)
    · exact absurd (he ▸ hadj) (fun hh => hx₂b hh)
    · rw [← hce] at hadj ⊢
      have := (PathBasics.path_adj_iff hP.1 hκ1lt hc).mp hadj
      exact gidx P (by omega) hc (by omega)
  have hRlen2 : 2 ≤ R.length := by
    by_contra hc
    have h1 : R.length = 1 := by omega
    have : (P[κ + 2]'(by omega)) = (P[κ - 1]'(by omega)) := by
      rw [← hR0, ← hRlst]; exact gidx R (by omega) hRpos (by omega)
    have := hnd.getElem_inj_iff.mp this
    omega
  have hRlen3 : 3 ≤ R.length := by
    by_contra hc
    have h2 : R.length = 2 := by omega
    have hadj := PathBasics.path_adj_succ hR.1 (show 0 + 1 < R.length by omega)
    rw [hR0, gidx R (show 0 + 1 = R.length - 1 by omega) (by omega) (by omega), hRlst] at hadj
    have := (PathBasics.path_adj_iff hP.1 (show κ + 2 < P.length by omega)
      (show κ - 1 < P.length by omega)).mp hadj
    omega
  have hC : IsHoleList G ((P[κ]'hκlt) :: (P[κ + 1]'hκ1lt) :: R) := by
    refine PrismBasics.isHoleList_of_path_add_two_vertices hR (by
      rw [PathBasics.pathLength_eq]; omega) ?_ ?_ hκadj.symm hκ1R hκR ?_ ?_ ?_ ?_
    · exact PathBasics.path_adj_succ hP.1 (show (κ + 1) + 1 < P.length by omega)
    · exact ((PathBasics.path_adj_iff hP.1 hκlt (show κ - 1 < P.length by omega)).mpr
        (Or.inr (by omega)))
    · intro hcon
      have := (PathBasics.path_adj_iff hP.1 hκ1lt (show κ - 1 < P.length by omega)).mp hcon
      omega
    · intro hcon
      have := (PathBasics.path_adj_iff hP.1 hκlt (show κ + 2 < P.length by omega)).mp hcon
      omega
    · intro z hz hcon
      have hzR : z ∈ R := PathBasics.interior_subset hz
      have hze := hκ1nbr z hzR hcon
      rw [PathBasics.mem_interior_iff_of_pathFrom hR] at hz
      exact hz.2.1 hze
    · intro z hz hcon
      have hzR : z ∈ R := PathBasics.interior_subset hz
      have hze := hκnbr z hzR hcon
      rw [PathBasics.mem_interior_iff_of_pathFrom hR] at hz
      exact hz.2.2 hze
  -- *"`C` has length ≥ 6"*
  have hClen : holeLength ((P[κ]'hκlt) :: (P[κ + 1]'hκ1lt) :: R) = R.length + 2 := by
    simp [holeLength]
  have hCeven : Even (holeLength ((P[κ]'hκlt) :: (P[κ + 1]'hκ1lt) :: R)) := hBerge.1 _ hC
  have hC6 : 6 ≤ holeLength ((P[κ]'hκlt) :: (P[κ + 1]'hκ1lt) :: R) := by
    rw [Nat.even_iff] at hCeven; omega
  -- `X k` is disjoint from `V(C)`
  have hCX : ∀ w ∈ ((P[κ]'hκlt) :: (P[κ + 1]'hκ1lt) :: R), w ∉ X k := by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hFX _ hκF k
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hFX _ hκ1F k
    rcases hRdec w hw with ⟨c, hc, -, hce⟩ | he | he | ⟨c, hc, -, hce⟩
    · rw [← hce]; exact hFX _ (hPF _ (List.getElem_mem hc)) k
    · rw [he]; exact Set.disjoint_left.mp (hXdisj i k hik) hx₁X
    · rw [he]; exact Set.disjoint_left.mp (hXdisj j k hjk) hx₂X
    · rw [← hce]; exact hFX _ (hPF _ (List.getElem_mem hc)) k
  -- the third `X k`-complete vertex of `C`
  obtain ⟨x, hxR, hxk, hxne1, hxne2⟩ :
      ∃ x : V, x ∈ R ∧ VertexComplete G x (X k) ∧ x ≠ P[κ]'hκlt ∧ x ≠ P[κ + 1]'hκ1lt := by
    rcases hRuses with h | h
    · exact ⟨x₁, h, hXcomp i k hik x₁ hx₁X, fun hh => hx₁P (hh ▸ List.getElem_mem hκlt),
        fun hh => hx₁P (hh ▸ List.getElem_mem hκ1lt)⟩
    · exact ⟨x₂, h, hXcomp j k hjk x₂ hx₂X, fun hh => hx₂P (hh ▸ List.getElem_mem hκlt),
        fun hh => hx₂P (hh ▸ List.getElem_mem hκ1lt)⟩
  have hκne : (P[κ]'hκlt) ≠ (P[κ + 1]'hκ1lt) :=
    PathBasics.path_ne_of_ne_index hP.1 hκlt hκ1lt (by omega)
  have he₀ : s((P[κ]'hκlt), (P[κ + 1]'hκ1lt)) ∈
      HoleYEdgeParity.yEdges G (X k) ((P[κ]'hκlt) :: (P[κ + 1]'hκ1lt) :: R) :=
    ⟨_, by simp, _, by simp, rfl, hκadj, hκk, hκ1k⟩
  -- the same cycle written in the other orientation, so that `p_{k-1}` sits at position 2
  have hCrev : IsHoleList G ((P[κ + 1]'hκ1lt) :: (P[κ]'hκlt) :: R.reverse) := by
    refine PrismBasics.isHoleList_of_path_add_two_vertices (PathBasics.isPathFrom_reverse hR)
      (by rw [PathBasics.pathLength_reverse, PathBasics.pathLength_eq]; omega) ?_ ?_ hκadj
      (fun h => hκR (List.mem_reverse.mp h)) (fun h => hκ1R (List.mem_reverse.mp h)) ?_ ?_ ?_ ?_
    · exact ((PathBasics.path_adj_iff hP.1 hκlt (show κ - 1 < P.length by omega)).mpr
        (Or.inr (by omega)))
    · exact PathBasics.path_adj_succ hP.1 (show (κ + 1) + 1 < P.length by omega)
    · intro hcon
      have := (PathBasics.path_adj_iff hP.1 hκlt (show κ + 2 < P.length by omega)).mp hcon
      omega
    · intro hcon
      have := (PathBasics.path_adj_iff hP.1 hκ1lt (show κ - 1 < P.length by omega)).mp hcon
      omega
    · intro z hz hcon
      have hzR : z ∈ R := List.mem_reverse.mp (PathBasics.interior_subset hz)
      have hze := hκnbr z hzR hcon
      rw [PathBasics.mem_interior_reverse, PathBasics.mem_interior_iff_of_pathFrom hR] at hz
      exact hz.2.2 hze
    · intro z hz hcon
      have hzR : z ∈ R := List.mem_reverse.mp (PathBasics.interior_subset hz)
      have hze := hκ1nbr z hzR hcon
      rw [PathBasics.mem_interior_reverse, PathBasics.mem_interior_iff_of_pathFrom hR] at hz
      exact hz.2.1 hze
  have hCrev6 : 6 ≤ holeLength ((P[κ + 1]'hκ1lt) :: (P[κ]'hκlt) :: R.reverse) := by
    simp only [holeLength, List.length_cons, List.length_reverse]
    simp only [holeLength, List.length_cons] at hC6
    omega
  -- three cyclically consecutive `X k`-complete vertices contradict `F₁₀`
  have hright : VertexComplete G (P[κ + 2]'(show κ + 2 < P.length by omega)) (X k) → False := by
    intro hcomp
    refine three_consecutive_absurd hG (hXne k) hC hC6 ?_ hκk hκ1k hcomp
    refine HoleArc.prefix_three (by simp only [List.length_cons]; omega) rfl rfl ?_
    simpa using hR0
  have hleft : VertexComplete G (P[κ - 1]'(show κ - 1 < P.length by omega)) (X k) → False := by
    intro hcomp
    refine three_consecutive_absurd hG (hXne k) hCrev hCrev6 ?_ hκ1k hκk hcomp
    refine HoleArc.prefix_three
      (by simp only [List.length_cons, List.length_reverse]; omega) rfl rfl ?_
    have h0 : R.reverse[0]'(by simp only [List.length_reverse]; omega) =
        P[κ - 1]'(show κ - 1 < P.length by omega) :=
      PathBasics.getElem_zero_of_head? (PathBasics.isPathFrom_reverse hR).2.1
        (by simp only [List.length_reverse]; omega)
    simpa using h0
  -- *"at least one edge of `C` is `X₃`-complete, namely `p_k p_{k+1}`, and at least one more
  -- vertex of it is `X₃`-complete"*: 2.3 forces a **second** `X k`-complete edge
  obtain ⟨e, hem, hene⟩ :=
    second_yEdge hBerge (hXanti k) hC hCX (by simp) (by simp)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hxR))
      hκne (Ne.symm hxne1) (Ne.symm hxne2) hκk hκ1k hxk he₀
  obtain ⟨pv, hpv, qv, hqv, rfl, hpqadj, hpvk, hqvk⟩ := hem
  rcases eq_or_ne pv (P[κ]'hκlt) with h1 | h1
  · subst h1
    have hqne : qv ≠ P[κ + 1]'hκ1lt := by
      intro h; exact hene (by rw [h])
    have hqR : qv ∈ R := by
      rcases List.mem_cons.mp hqv with h | h
      · exact absurd (h ▸ hpqadj) G.irrefl
      rcases List.mem_cons.mp h with h' | h'
      · exact absurd h' hqne
      · exact h'
    exact hleft (by rw [← hκnbr qv hqR hpqadj]; exact hqvk)
  rcases eq_or_ne qv (P[κ]'hκlt) with h2 | h2
  · subst h2
    have hpne : pv ≠ P[κ + 1]'hκ1lt := by
      intro h; exact hene (by rw [h]; exact Sym2.eq_swap)
    have hpR : pv ∈ R := by
      rcases List.mem_cons.mp hpv with h | h
      · exact absurd (h ▸ hpqadj.symm) G.irrefl
      rcases List.mem_cons.mp h with h' | h'
      · exact absurd h' hpne
      · exact h'
    exact hleft (by rw [← hκnbr pv hpR hpqadj.symm]; exact hpvk)
  rcases eq_or_ne pv (P[κ + 1]'hκ1lt) with h3 | h3
  · subst h3
    have hqR : qv ∈ R := by
      rcases List.mem_cons.mp hqv with h | h
      · exact absurd h h2
      rcases List.mem_cons.mp h with h' | h'
      · exact absurd (h' ▸ hpqadj) G.irrefl
      · exact h'
    exact hright (by rw [← hκ1nbr qv hqR hpqadj]; exact hqvk)
  rcases eq_or_ne qv (P[κ + 1]'hκ1lt) with h4 | h4
  · subst h4
    have hpR : pv ∈ R := by
      rcases List.mem_cons.mp hpv with h | h
      · exact absurd h h1
      rcases List.mem_cons.mp h with h' | h'
      · exact absurd (h' ▸ hpqadj.symm) G.irrefl
      · exact h'
    exact hright (by rw [← hκ1nbr pv hpR hpqadj.symm]; exact hpvk)
  -- *"contrary to `G ∈ F₉`"*: two disjoint `X k`-complete edges of a hole of length `≥ 6`
  exact hG.1.1.2.1 ⟨_, X k, ⟨hC, hC6⟩, ⟨hXne k, hXanti k, hCX⟩,
    ⟨P[κ]'hκlt, P[κ + 1]'hκ1lt, pv, qv, by simp, by simp, hpv, hqv,
      ⟨hκadj, hκk, hκ1k⟩, ⟨hpqadj, hpvk, hqvk⟩, Ne.symm h1, Ne.symm h2, Ne.symm h3,
      Ne.symm h4⟩⟩

end Workspace.Types.Thm244Case3
