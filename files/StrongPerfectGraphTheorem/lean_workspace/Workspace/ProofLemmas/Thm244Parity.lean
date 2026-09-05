import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.HoleArc
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.Statements.S13.Thm_13_7

/-!
# Claim (1) inside the printed proof of 24.4

Chudnovsky–Robertson–Seymour–Thomas, *The Strong Perfect Graph Theorem*, printed
p. 144, inside the proof of 24.4:

> (1) *If `p₁-⋯-pₙ` is a path in `F`, and `p₁` is its unique `X₁`-complete vertex
> and `pₙ` is its unique `X₂`-complete vertex then `n` is even.*
>
> For `n > 1`, since no vertex is both `X₁`-complete and `X₂`-complete.  Assume `n`
> is odd; then by 13.7, `n = 3`.  But there is an antipath `Q₁` between `p₂,p₃` with
> interior in `X₁`, and an antipath `Q₂` between `p₁,p₂` with interior in `X₂`; and
> then `p₂-Q₁-p₃-p₁-Q₂-p₂` is an antihole of length `> 4`, a contradiction.  This
> proves (1).

Transcribed step for step.

* *"For `n > 1`"* — the printed reason (*"since no vertex is both `X₁`-complete and
  `X₂`-complete"*) is the ambient hypothesis of 24.4, which claim (1) does not carry.
  Here it is replaced by the equivalent, self-contained hypothesis `p₁ ≠ pₙ`, which
  is what every call site of (1) inside 24.4 supplies (the two ends of the path are
  the two distinct vertices `vᵢ, vⱼ`).
* *"Assume `n` is odd; then by 13.7, `n = 3`"* — `n` odd means `pathLength p = n - 1`
  is even, and `n > 1` means it is positive, so 13.7 applies verbatim and returns
  `pathLength p = 2` together with the two antipaths.
* The two antipaths returned by 13.7 are exactly the printed `Q₁` (from `p₂` to `p₃`,
  interior in `X₁`) and `Q₂` (from `p₁` to `p₂`, interior in `X₂`).  Their union
  `p₂-Q₁-p₃-p₁-Q₂-p₂` is the list `Q₁ ++ Q₂.dropLast` (`PathGlue.glue_hole` at `Gᶜ`),
  an antihole of length `pathLength Q₁ + pathLength Q₂ + 1 ≥ 5`, whereas `G ∈ F₁₁`
  forces every antihole to have length `4`.
  (`pathLength Qᵢ ≥ 2` because the two ends of each `Qᵢ` are *adjacent* in `G`, being
  consecutive on the path `p`, hence non-adjacent in `Gᶜ`.)

The parity clause `Xor' (Odd (pathLength Q)) (Odd (pathLength R))` that 13.7 also
returns is not used; the length of the antihole alone gives the contradiction.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm244Parity

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*}

/-- Rewriting the *index* of a `getElem` is a motive error; this is the usable form. -/
private theorem gidx {W : Type*} (q : List W) {a b : ℕ} (h : a = b)
    (ha : a < q.length) (hb : b < q.length) : q[a]'ha = q[b]'hb := by
  subst h; rfl

/-- **Deleting the last vertex of a path leaves a path.**

Stated with an explicit membership decoder so that no `slice` expression escapes into
the caller's goal, and so that the caller can read off the index of any vertex of the
truncated path.  Degenerate case included: a two-vertex path truncates to a
one-vertex path.

This is the shape every *"`p₁-Q-pₙ-⋯`"* concatenation in §24 needs, since gluing two
paths that share an endpoint means dropping that endpoint from one of them. -/
theorem chop {K : SimpleGraph V} {R : List V} {a b : V}
    (hR : IsPathFrom K R a b) (h2 : 2 ≤ R.length) :
    ∃ D : List V, IsPathFrom K D a (R[R.length - 2]'(by omega)) ∧
      D.length = R.length - 1 ∧
      (∀ y, y ∈ D ↔ ∃ (k : ℕ) (hk : k < R.length), k ≤ R.length - 2 ∧ R[k]'hk = y) := by
  have hpos : 0 < R.length := by omega
  have hm : R.length - 2 < R.length := by omega
  have hR0 : R[0]'hpos = a := PathBasics.getElem_zero_of_head? hR.2.1 hpos
  rcases (show R.length = 2 ∨ 3 ≤ R.length by omega) with h2' | h3
  · -- a two-vertex path truncates to the singleton `[a]`
    have hae : R[R.length - 2]'hm = a := by rw [← hR0]; exact gidx R (by omega) hm hpos
    refine ⟨[a], ⟨PathBasics.isPathList_singleton K a, rfl, ?_⟩, by simp; omega, ?_⟩
    · simp [hae]
    · intro y
      simp only [List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨0, hpos, by omega, hR0⟩
      · rintro ⟨k, hk, hkm, hky⟩
        rw [← hky, ← hR0]
        exact gidx R (by omega) hk hpos
  · have h0m : 0 < R.length - 2 := by omega
    refine ⟨(R.drop 0).take (R.length - 2 - 0 + 1), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · exact PathBasics.isPathList_slice hR.1 h0m hm
    · rw [PathBasics.head?_slice R (le_of_lt h0m) hm]
      exact congrArg some hR0
    · exact PathBasics.getLast?_slice R (le_of_lt h0m) hm
    · rw [PathBasics.length_slice R (le_of_lt h0m) hm]; omega
    · intro y
      rw [PathBasics.mem_slice_iff R (le_of_lt h0m) hm]
      constructor
      · rintro ⟨k, hk, -, hkm, hky⟩; exact ⟨k, hk, hkm, hky⟩
      · rintro ⟨k, hk, hkm, hky⟩; exact ⟨k, hk, Nat.zero_le _, hkm, hky⟩

/-- **Claim (1) of the printed proof of 24.4.**

`G ∈ F₁₁`; `X, Y` are disjoint nonempty anticonnected sets complete to each other;
`p` is a path of `G` with distinct ends `p₁, pₙ` such that `p₁` is the **unique**
`X`-complete vertex of `p` and `pₙ` is the **unique** `Y`-complete vertex of `p`.
Then the *number of vertices* of `p` is even.

(The paper's `n` is `p.length`; its `X₁, X₂` are `X, Y` here, so that the statement
can be applied to any of the three pairs drawn from `X₁, X₂, X₃`.) -/
theorem even_length_of_unique_ends [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : InF11 G) (X Y : Set V)
    (hXY : Disjoint X Y) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXa : AnticonnectedSet G X) (hYa : AnticonnectedSet G Y)
    (hcompl : Complete G X Y)
    (p : List V) (p₁ pₙ : V) (hp : IsPathList G p)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pₙ) (hne : p₁ ≠ pₙ)
    (hXuniq : ∀ w ∈ p, (VertexComplete G w X ↔ w = p₁))
    (hYuniq : ∀ w ∈ p, (VertexComplete G w Y ↔ w = pₙ)) :
    Even p.length := by
  by_contra hcon
  rw [Nat.not_even_iff_odd] at hcon
  have hpos : 0 < p.length := PathBasics.path_length_pos hp
  have h0 : p[0]'hpos = p₁ := PathBasics.getElem_zero_of_head? hhead hpos
  have hlst : p[p.length - 1]'(by omega) = pₙ :=
    PathBasics.getElem_last_of_getLast? hlast hpos
  have hlen2 : 2 ≤ p.length := by
    by_contra hc
    refine hne ?_
    rw [← h0, ← hlst]
    exact gidx p (by omega) hpos (by omega)
  have heven : Even (pathLength p) := by
    rw [PathBasics.pathLength_eq]
    obtain ⟨m, hm⟩ := hcon
    exact ⟨m, by omega⟩
  have hposL : 0 < pathLength p := by rw [PathBasics.pathLength_eq]; omega
  -- *"then by 13.7, `n = 3`"*, together with the two antipaths it produces.
  obtain ⟨-, c, hpc, Q, R, ⟨hQ, hQint⟩, ⟨hR, hRint⟩, -⟩ :=
    _root_.Workspace.Statements.S13.SPGT.thm_13_7 G (HoleArc.inF5_of_inF11 hG) X Y hXY hXne
      hYne hXa hYa hcompl p p₁ pₙ hp heven hposL hhead hlast hXuniq hYuniq
  subst hpc
  -- the three vertices of `p`, and the adjacencies along it
  have hlen3 : ([p₁, c, pₙ] : List V).length = 3 := by simp
  have hadj1 : G.Adj p₁ c := by
    have h := (PathBasics.path_adj_iff hp (i := 0) (j := 1) (by simp) (by simp)).mpr (Or.inl rfl)
    simpa using h
  have hadj2 : G.Adj c pₙ := by
    have h := (PathBasics.path_adj_iff hp (i := 1) (j := 2) (by simp) (by simp)).mpr (Or.inl rfl)
    simpa using h
  have hnadj : ¬ G.Adj p₁ pₙ := by
    intro h
    have h2 := (PathBasics.path_adj_iff hp (i := 0) (j := 2) (by simp) (by simp)).mp (by simpa using h)
    omega
  have hne₁c : p₁ ≠ c := hadj1.ne
  have hnecn : c ≠ pₙ := hadj2.ne
  have hmem₁ : p₁ ∈ ([p₁, c, pₙ] : List V) := by simp
  have hmemc : c ∈ ([p₁, c, pₙ] : List V) := by simp
  have hmemn : pₙ ∈ ([p₁, c, pₙ] : List V) := by simp
  have hp₁X : VertexComplete G p₁ X := (hXuniq p₁ hmem₁).mpr rfl
  have hpnY : VertexComplete G pₙ Y := (hYuniq pₙ hmemn).mpr rfl
  have hp₁notX : p₁ ∉ X := fun h => G.irrefl (hp₁X p₁ h)
  have hpnnotY : pₙ ∉ Y := fun h => G.irrefl (hpnY pₙ h)
  have hpnnotX : pₙ ∉ X := fun h => hnadj (hp₁X pₙ h)
  have hp₁notY : p₁ ∉ Y := fun h => hnadj (hpnY p₁ h).symm
  have hcnotX : c ∉ X := by
    intro h
    exact hnecn ((hYuniq c hmemc).mp (hcompl c h))
  have hcnotY : c ∉ Y := by
    intro h
    exact hne₁c ((hXuniq c hmemc).mp (fun x hx => (hcompl x hx c h).symm)).symm
  -- the two antipaths, read as paths of `Gᶜ`
  have hQ' : IsPathFrom Gᶜ Q c pₙ := hQ
  have hR' : IsPathFrom Gᶜ R p₁ c := hR
  have hQ3 : 3 ≤ Q.length := by
    refine MinimalConnectedIsPath.three_le_length_of_not_adj hQ' hnecn ?_
    rw [SimpleGraph.compl_adj]
    push_neg
    intro _
    exact hadj2
  have hR3 : 3 ≤ R.length := by
    refine MinimalConnectedIsPath.three_le_length_of_not_adj hR' hne₁c ?_
    rw [SimpleGraph.compl_adj]
    push_neg
    intro _
    exact hadj1
  have hQnd : Q.Nodup := PathBasics.path_nodup hQ'.1
  have hRnd : R.Nodup := PathBasics.path_nodup hR'.1
  have hQpos : 0 < Q.length := by omega
  have hRpos : 0 < R.length := by omega
  have hQ0 : Q[0]'hQpos = c := PathBasics.getElem_zero_of_head? hQ'.2.1 hQpos
  have hQl : Q[Q.length - 1]'(by omega) = pₙ :=
    PathBasics.getElem_last_of_getLast? hQ'.2.2 hQpos
  have hR0 : R[0]'hRpos = p₁ := PathBasics.getElem_zero_of_head? hR'.2.1 hRpos
  have hRl : R[R.length - 1]'(by omega) = c :=
    PathBasics.getElem_last_of_getLast? hR'.2.2 hRpos
  -- chop the last vertex `c` off `R`, so that `Q ++ D` is the printed cycle
  obtain ⟨D, hD, hDlen, hDmem⟩ := chop hR' (by omega)
  have hmlt : R.length - 2 < R.length := by omega
  -- interior decoders
  have hQdec : ∀ x ∈ Q, x = c ∨ x = pₙ ∨ x ∈ X := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := List.getElem_of_mem hx
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    · exact Or.inl (by rw [← hax]; exact hQ0)
    · by_cases haL : a + 1 = Q.length
      · refine Or.inr (Or.inl ?_)
        rw [← hax, gidx Q (show a = Q.length - 1 by omega) ha (by omega)]
        exact hQl
      · exact Or.inr (Or.inr (by
          rw [← hax]
          exact hQint _ (PathBasics.getElem_mem_interior hQ'.1 ha ha0 (by omega))))
  have hDdec : ∀ y ∈ D, y = p₁ ∨ y ∈ Y := by
    intro y hy
    obtain ⟨k, hk, hkm, hky⟩ := (hDmem y).mp hy
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact Or.inl (by rw [← hky]; exact hR0)
    · exact Or.inr (by
        rw [← hky]
        exact hRint _ (PathBasics.getElem_mem_interior hR'.1 hk hk0 (by omega)))
  -- the two paths are disjoint
  have hdisj : ∀ x ∈ Q, x ∉ D := by
    intro x hx hxD
    rcases hQdec x hx with hxc | hxn | hxX
    · subst hxc
      rcases hDdec x hxD with hy | hy
      · exact hne₁c hy.symm
      · exact hcnotY hy
    · subst hxn
      rcases hDdec x hxD with hy | hy
      · exact hne hy.symm
      · exact hpnnotY hy
    · rcases hDdec x hxD with hy | hy
      · subst hy; exact hp₁notX hxX
      · exact (Set.disjoint_left.mp hXY hxX) hy
  -- the only two cross edges are `pₙ p₁` and `c – R[R.length-2]`
  have hcross : ∀ x ∈ Q, ∀ y ∈ D,
      (Gᶜ.Adj x y ↔ (x = pₙ ∧ y = p₁) ∨ (x = c ∧ y = R[R.length - 2]'hmlt)) := by
    intro x hx y hy
    obtain ⟨k, hk, hkm, hky⟩ := (hDmem y).mp hy
    obtain ⟨a, ha, hax⟩ := List.getElem_of_mem hx
    subst hax
    subst hky
    have eQn : (Q[a]'ha = pₙ) ↔ a = Q.length - 1 := by
      rw [← hQl]; exact hQnd.getElem_inj_iff
    have eQc : (Q[a]'ha = c) ↔ a = 0 := by
      rw [← hQ0]; exact hQnd.getElem_inj_iff
    have eR1 : (R[k]'hk = p₁) ↔ k = 0 := by
      rw [← hR0]; exact hRnd.getElem_inj_iff
    have eRm : (R[k]'hk = R[R.length - 2]'hmlt) ↔ k = R.length - 2 := hRnd.getElem_inj_iff
    rw [eQn, eQc, eR1, eRm]
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    · -- `x = c`
      rw [hQ0, ← hRl, PathBasics.path_adj_iff hR'.1 (by omega) hk]
      omega
    · by_cases haL : a + 1 = Q.length
      · -- `x = pₙ`
        rw [gidx Q (show a = Q.length - 1 by omega) ha (by omega), hQl]
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · rw [hR0]
          refine iff_of_true ?_ (Or.inl ⟨by omega, rfl⟩)
          rw [SimpleGraph.compl_adj]
          exact ⟨fun h => hne h.symm, fun h => hnadj h.symm⟩
        · refine iff_of_false ?_ (by omega)
          rw [SimpleGraph.compl_adj]
          push_neg
          intro _
          exact hpnY _ (hRint _ (PathBasics.getElem_mem_interior hR'.1 hk hk0 (by omega)))
      · -- `x` is an interior vertex of `Q`, so `x ∈ X`
        have hxX : (Q[a]'ha) ∈ X :=
          hQint _ (PathBasics.getElem_mem_interior hQ'.1 ha ha0 (by omega))
        refine iff_of_false ?_ (by omega)
        rw [SimpleGraph.compl_adj]
        push_neg
        intro _
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · rw [hR0]; exact (hp₁X _ hxX).symm
        · exact hcompl _ hxX _ (hRint _ (PathBasics.getElem_mem_interior hR'.1 hk hk0 (by omega)))
  -- glue, and count
  have hhole : IsHoleList Gᶜ (Q ++ D) :=
    PathGlue.glue_hole hQ' hD hdisj hcross (by omega)
  have h4 := HoleArc.antihole_length_of_inF11 hG (Q ++ D) hhole
  simp only [holeLength, List.length_append] at h4
  omega

end Workspace.ProofLemmas.Thm244Parity
