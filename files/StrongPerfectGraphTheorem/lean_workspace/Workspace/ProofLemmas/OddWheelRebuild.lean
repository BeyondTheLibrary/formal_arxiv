import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.SegmentBasics
import Workspace.ProofLemmas.YEdgeConfiguration
import Workspace.ProofLemmas.OddWheelParityFacts
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.OptimalWheelChoice

/-!
# Rebuilding the rim: the closing paragraph of 16.3

PAPER (16.3, printed p. 101), the last five sentences of the proof:

> *"By 16.2 and (1), there is a 3-vertex path `p₁-p₂-p₃` in `C`, all `Y`-complete, and a path
> `p₁-f₁-⋯-f_k-p₃` with interior in `F`, such that there are no edges between `{f₁,…,f_k}` and
> `{p₄,…,pₙ}`.  But then `C \ p₂` can be completed to a hole `C'` say, via `p₁-f₁-⋯-f_k-p₃`; and
> `C'` has length `≥ 6`.  For every odd segment `S` of `(C,Y)`, either it contained both or
> neither of the edges `p₁p₂`, `p₂p₃`; and so in either case an odd number of edges of `S`
> belong to `C'`.  Since `(C,Y)` has an odd segment and there are an even number of `Y`-complete
> edges in `C`, it has at least two odd segments.  It follows that there are two disjoint
> `Y`-complete edges in `C'`, and so `(C',Y)` is a wheel.  Since an odd number of edges of the
> odd segment `S` belong to `C'`, it follows that `(C',Y)` is an odd wheel, contrary to the
> optimality of `(C,Y)`."*

`contradiction_from_bullet_three` is that paragraph: it takes the third bullet of `thm_16_2`
verbatim, together with the minimality clause of the optimality of `(C,Y)`, and derives `False`.

## How the printed argument is realised

Write `n = |C|` and put the rim in the frame in which `p₃, …, p₁` occupy positions
`0, …, n-2` and the deleted vertex `p₂` occupies the missing position `n-1`; concretely, with
`r = q+2` for the rotation `q` witnessing `[p₁,p₂,p₃] <+: C.rotate q`, position `i` of the new
hole is position `(i+r) mod n` of `C`.

* **`C \ p₂` is a path.**  It is the proper cyclic arc `A = (C.rotate r).take (n-1)`, a path
  from `p₃` to `p₁` by `WheelParity.arc_isPathFrom`, whose vertices are exactly the vertices of
  `C` other than `p₂`.
* **The new hole.**  `C' = A ++ P*`, assembled by `PathGlue.glue_hole`.  The cross condition —
  the only edges between `A` and `P*` are `p₁f₁` and `p₃f_k` — is exactly the bullet's
  *"there are no edges between `{f₁,…,f_k}` and `{p₄,…,pₙ}`"* (`hPno`) plus inducedness of `P`.
  `|C'| = (n-1) + |P*| ≥ 6`.
* **The `Y`-complete vertices of `C'`** are those of `C` except `p₂`: no `fᵢ` is `Y`-complete,
  since the `fᵢ` lie in `F` (`hFnc`).  This is `cvE1`/`cvE2` inside the proof.
* **The count.**  The `Y`-complete cyclic edges of `C'` are the `Y`-complete cyclic edges of `C`
  other than `p₁p₂` and `p₂p₃`, so
  `yEdgeCount G Y C' = yEdgeCount G Y C - 2` — the strict decrease.
* **The odd segment survives.**  An odd segment of `(C,Y)` — a maximal run of *even* length
  `L` of `Y`-complete positions — either misses `p₂`, and is then still a maximal run of `C'`;
  or contains `p₂`, and is then cut by the deletion into two maximal runs of `C'` of sizes
  summing to `L-1`, an odd number, so one of the two has even size.  (Both pieces are non-empty
  because `p₁` and `p₃`, being `Y`-complete, lie in that run.)  Either way `(C',Y)` has a
  maximal run of even length, i.e. an odd `Y`-segment.
* **Two disjoint `Y`-complete edges.**  That run carries an odd number `Λ-1 ≥ 1` of the
  `Y`-complete edges of `C'`, while the *total* number of them is even (it is two less than the
  even total for `C`, by 2.3 via `WheelBasics.even_cycCount_of_wheel`).  Hence some `Y`-complete
  edge of `C'` lies outside the run, and its two ends are distinct from the run's — the paper's
  *"it has at least two odd segments … it follows that there are two disjoint `Y`-complete edges
  in `C'`"*, with the parity bookkeeping done on `C'` rather than on `C`.
* So `(C',Y)` is an odd wheel with two fewer `Y`-complete rim edges than `(C,Y)`, contradicting
  the minimality clause `hmin`.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Workspace.ProofLemmas.OddWheelRebuild

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {C : List V} {Y : Set V}

private theorem mod_cancel_add_right {n a b c : ℕ} (h : (a + c) % n = (b + c) % n) :
    a % n = b % n := Nat.ModEq.add_right_cancel' c h

private theorem mod_cancel_add_left {n a b c : ℕ} (h : (c + a) % n = (c + b) % n) :
    a % n = b % n := Nat.ModEq.add_left_cancel' c h

/-- A `Y`-complete cyclic edge, read as an `EdgeComplete` fact about its two ends. -/
private theorem edgeComplete_of_cycEdge {L : List V} (hL : 0 < L.length) {m : ℕ}
    (h : WheelParity.CycEdge G Y L m) :
    EdgeComplete G Y (L[m % L.length]'(Nat.mod_lt _ hL))
      (L[(m + 1) % L.length]'(Nat.mod_lt _ hL)) := by
  obtain ⟨u, v, hu, hv, hec⟩ := h
  rw [List.getElem?_eq_getElem (Nat.mod_lt _ hL)] at hu hv
  rw [Option.some_inj.mp hu, Option.some_inj.mp hv]
  exact hec

/-- An odd wheel has a maximal run of `Y`-complete rim positions of **even** length. -/
private theorem exists_even_run (hBerge : Berge G) (hodd : IsOddWheel G C Y) :
    ∃ k L : ℕ, 2 ≤ L ∧ Even L ∧ L + 1 ≤ C.length ∧
      (∀ t < L, SegmentBasics.CycVert G Y C (k + t)) ∧
      ¬ SegmentBasics.CycVert G Y C (k + L) ∧
      ¬ SegmentBasics.CycVert G Y C (k + (C.length - 1)) := by
  have hw : IsWheel G C Y := hodd.1
  have hC : IsHoleList G C := hw.1.1
  have hn6 : 6 ≤ C.length := hw.1.2
  have hn : 0 < C.length := by omega
  have heven := WheelBasics.even_cycCount_of_wheel hBerge hw
  obtain ⟨-, S, hS, hSodd⟩ := hodd
  obtain ⟨k, hL1, hLn, hall⟩ := OddWheelParityFacts.isSegment_arc hC hS
  have hLeven : Even S.length := (SegmentBasics.odd_pathLength_iff_even_length hL1).mp hSodd
  have hLn2 : S.length + 2 ≤ C.length := by
    by_contra hcon
    have hLeq : C.length = S.length + 1 := by omega
    by_cases hfull : SegmentBasics.CycVert G Y C (k + S.length)
    · have hallpos : ∀ m : ℕ, SegmentBasics.CycVert G Y C m := by
        intro m
        obtain ⟨t, ht, hteq⟩ := OddWheelParityFacts.exists_offset hn k m
        refine (SegmentBasics.cycVert_congr hteq).mp ?_
        rcases Nat.lt_or_ge t S.length with h | h
        · exact hall t h
        · have htt : t = S.length := by omega
          rw [htt]; exact hfull
      have hcc : WheelParity.cycCount G Y C C.length = C.length :=
        OddWheelParityFacts.cycCount_full (fun m =>
          (YEdgeConfiguration.cycEdge_iff hC).mpr ⟨hallpos m, hallpos (m + 1)⟩)
      rw [hcc] at heven
      obtain ⟨e, he⟩ := hLeven
      obtain ⟨f, hf⟩ := heven
      omega
    · have hcc := OddWheelParityFacts.cycCount_run hC hall hfull
      have hcc2 : WheelParity.cycCount G Y C (k + C.length)
          = WheelParity.cycCount G Y C (k + S.length) + 0 := by
        rw [show k + C.length = (k + S.length) + 1 by omega, WheelParity.cycCount_succ,
          if_neg (YEdgeConfiguration.not_cycEdge_at_run_end hC hfull)]
      rw [WheelParity.cycCount_add_length] at hcc2
      obtain ⟨e, he⟩ := hLeven
      obtain ⟨f, hf⟩ := heven
      omega
  obtain ⟨k', -, hall', hnext', hprev', -⟩ := SegmentBasics.isSegment_run hC hS hLn2
  obtain ⟨e, he⟩ := hLeven
  exact ⟨k', S.length, by omega, ⟨e, he⟩, by omega, hall', hnext', hprev'⟩

/-- The closing paragraph of the printed proof of 16.3, with the three cyclically consecutive
`Y`-complete vertices given in the forward orientation `[p₁,p₂,p₃] <+: C.rotate q`. -/
private theorem core (hBerge : Berge G) (hodd : IsOddWheel G C Y)
    (hmin : ∀ C' : List V, IsOddWheel G C' Y →
      OptimalWheelChoice.yEdgeCount G Y C ≤ OptimalWheelChoice.yEdgeCount G Y C')
    (F : Set V) (hFC : ∀ f ∈ F, f ∉ C) (hFY : ∀ f ∈ F, f ∉ Y)
    (hFnc : ∀ f ∈ F, ¬ VertexComplete G f Y)
    (p₁ p₂ p₃ : V) (q : ℕ) (hblock : [p₁, p₂, p₃] <+: C.rotate q)
    (h₁ : VertexComplete G p₁ Y) (h₂ : VertexComplete G p₂ Y) (h₃ : VertexComplete G p₃ Y)
    (P : List V) (hP : IsPathFrom G P p₁ p₃) (hPF : ∀ x ∈ SPGT.interior P, x ∈ F)
    (hPno : ∀ x ∈ SPGT.interior P, ∀ u ∈ C, u ≠ p₁ → u ≠ p₂ → u ≠ p₃ → ¬ G.Adj x u) :
    False := by
  classical
  have hw : IsWheel G C Y := hodd.1
  have hC : IsHoleList G C := hw.1.1
  have hn6 : 6 ≤ C.length := hw.1.2
  have hn : 0 < C.length := by omega
  have hnd : C.Nodup := hC.2.1
  have hCY : ∀ v ∈ C, v ∉ Y := hw.2.1.2.2
  have hYne : Y.Nonempty := hw.2.1.1
  have hYanti : AnticonnectedSet G Y := hw.2.1.2.1
  have heven : Even (WheelParity.cycCount G Y C C.length) :=
    WheelBasics.even_cycCount_of_wheel hBerge hw
  have gidx : ∀ (a b : ℕ) (ha : a < C.length) (hb : b < C.length), a = b →
      (C[a]'ha) = (C[b]'hb) := by intro a b ha hb h; subst h; rfl
  have hmodeq : ∀ a b : ℕ, a = b → a % C.length = b % C.length := by
    intro a b h; rw [h]
  ------------------------------------------------------------------
  -- the positions of p₁, p₂, p₃ on the rim
  ------------------------------------------------------------------
  have hrlen : (C.rotate q).length = C.length := by simp
  have hr0 : (0 : ℕ) < (C.rotate q).length := by omega
  have hr1 : (1 : ℕ) < (C.rotate q).length := by omega
  have hr2 : (2 : ℕ) < (C.rotate q).length := by omega
  have hq0 : ((C.rotate q)[0]'hr0) = p₁ := by
    simpa using (hblock.getElem (i := 0) (by simp)).symm
  have hq1 : ((C.rotate q)[1]'hr1) = p₂ := by
    simpa using (hblock.getElem (i := 1) (by simp)).symm
  have hq2 : ((C.rotate q)[2]'hr2) = p₃ := by
    simpa using (hblock.getElem (i := 2) (by simp)).symm
  have hc0 : (C[(0 + q) % C.length]'(Nat.mod_lt _ hn)) = p₁ :=
    (WheelParity.getElem_rotate_eq hn hr0).symm.trans hq0
  have hc1 : (C[(1 + q) % C.length]'(Nat.mod_lt _ hn)) = p₂ :=
    (WheelParity.getElem_rotate_eq hn hr1).symm.trans hq1
  have hc2 : (C[(2 + q) % C.length]'(Nat.mod_lt _ hn)) = p₃ :=
    (WheelParity.getElem_rotate_eq hn hr2).symm.trans hq2
  obtain ⟨r, hrdef⟩ : ∃ r : ℕ, r = q + 2 := ⟨_, rfl⟩
  have hpos3 : (C[(0 + r) % C.length]'(Nat.mod_lt _ hn)) = p₃ :=
    (gidx _ _ (Nat.mod_lt _ hn) (Nat.mod_lt _ hn)
      (hmodeq (0 + r) (2 + q) (by omega))).trans hc2
  have hpos1 : (C[(C.length - 2 + r) % C.length]'(Nat.mod_lt _ hn)) = p₁ := by
    refine Eq.trans (gidx _ _ (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) ?_) hc0
    rw [hrdef, show C.length - 2 + (q + 2) = C.length + (0 + q) from by omega, Nat.add_mod_left]
  have hpos2 : (C[(C.length - 1 + r) % C.length]'(Nat.mod_lt _ hn)) = p₂ := by
    refine Eq.trans (gidx _ _ (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) ?_) hc1
    rw [hrdef, show C.length - 1 + (q + 2) = C.length + (1 + q) from by omega, Nat.add_mod_left]
  ------------------------------------------------------------------
  -- shifted index toolkit
  ------------------------------------------------------------------
  have hshift_ne : ∀ a b : ℕ, a < C.length → b < C.length → a ≠ b →
      (C[(a + r) % C.length]'(Nat.mod_lt _ hn)) ≠ (C[(b + r) % C.length]'(Nat.mod_lt _ hn)) := by
    intro a b ha hb hab
    refine HoleBasics.hole_ne_of_ne_index hC _ _ ?_
    intro h
    have h2 : a % C.length = b % C.length := mod_cancel_add_right h
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
    exact hab h2
  have hshift_adj : ∀ a b : ℕ, a < C.length → b < C.length →
      (G.Adj (C[(a + r) % C.length]'(Nat.mod_lt _ hn))
          (C[(b + r) % C.length]'(Nat.mod_lt _ hn)) ↔
        (b = (a + 1) % C.length ∨ a = (b + 1) % C.length)) := by
    intro a b ha hb
    rw [HoleBasics.hole_adj_iff hC (Nat.mod_lt _ hn) (Nat.mod_lt _ hn), Nat.mod_add_mod,
      Nat.mod_add_mod]
    have e1 : ((b + r) % C.length = (a + r + 1) % C.length) ↔ b = (a + 1) % C.length := by
      rw [show a + r + 1 = (a + 1) + r from by omega]
      constructor
      · intro h
        have h2 : b % C.length = (a + 1) % C.length := mod_cancel_add_right h
        rwa [Nat.mod_eq_of_lt hb] at h2
      · intro h
        have h2 : b % C.length = (a + 1) % C.length := by rw [Nat.mod_eq_of_lt hb]; exact h
        exact SegmentBasics.add_mod_congr h2 r
    have e2 : ((a + r) % C.length = (b + r + 1) % C.length) ↔ a = (b + 1) % C.length := by
      rw [show b + r + 1 = (b + 1) + r from by omega]
      constructor
      · intro h
        have h2 : a % C.length = (b + 1) % C.length := mod_cancel_add_right h
        rwa [Nat.mod_eq_of_lt ha] at h2
      · intro h
        have h2 : a % C.length = (b + 1) % C.length := by rw [Nat.mod_eq_of_lt ha]; exact h
        exact SegmentBasics.add_mod_congr h2 r
    rw [e1, e2]
  have hcv_shift : ∀ a : ℕ, (SegmentBasics.CycVert G Y C (a + r) ↔
      VertexComplete G (C[(a + r) % C.length]'(Nat.mod_lt _ hn)) Y) := by
    intro a
    constructor
    · rintro ⟨u, hu, huY⟩
      rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn)] at hu
      rw [Option.some_inj.mp hu]
      exact huY
    · intro h
      exact ⟨_, List.getElem?_eq_getElem (Nat.mod_lt _ hn), h⟩
  have hcvp1 : SegmentBasics.CycVert G Y C (C.length - 2 + r) :=
    (hcv_shift _).mpr (by rw [hpos1]; exact h₁)
  have hcvp2 : SegmentBasics.CycVert G Y C (C.length - 1 + r) :=
    (hcv_shift _).mpr (by rw [hpos2]; exact h₂)
  have hcvp3 : SegmentBasics.CycVert G Y C (0 + r) :=
    (hcv_shift _).mpr (by rw [hpos3]; exact h₃)
  ------------------------------------------------------------------
  -- the arc  A = C minus p₂
  ------------------------------------------------------------------
  obtain ⟨A, hAdef⟩ : ∃ A : List V, A = (C.rotate r).take (C.length - 1) := ⟨_, rfl⟩
  have hAlen : A.length = C.length - 1 := by
    rw [hAdef]; simp only [List.length_take, List.length_rotate]; omega
  have hAget : ∀ (t : ℕ) (ht : t < A.length),
      (A[t]'ht) = C[(t + r) % C.length]'(Nat.mod_lt _ hn) := by
    subst hAdef
    intro t ht
    rw [SegmentBasics.arc_getElem hn ht]
    exact gidx _ _ (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) (hmodeq (r + t) (t + r) (by omega))
  have hApath : IsPathFrom G A p₃ p₁ := by
    rw [← hpos3, ← hpos1, hAdef]
    exact WheelParity.arc_isPathFrom hC (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) (by omega) (by omega)
      (hmodeq r (0 + r) (by omega)) (hmodeq (r + (C.length - 1) - 1) (C.length - 2 + r) (by omega))
  have hAmem : ∀ x : V, x ∈ A ↔ (x ∈ C ∧ x ≠ p₂) := by
    intro x
    constructor
    · intro hx
      obtain ⟨t, ht, htx⟩ := List.getElem_of_mem hx
      rw [hAget t ht] at htx
      refine ⟨htx ▸ List.getElem_mem _, ?_⟩
      rw [← htx, ← hpos2]
      exact hshift_ne t (C.length - 1) (by omega) (by omega) (by omega)
    · rintro ⟨hxC, hxp⟩
      obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hxC
      obtain ⟨t, ht, hteq⟩ := OddWheelParityFacts.exists_offset hn r i
      have htlt : t < C.length - 1 := by
        rcases Nat.lt_or_ge t (C.length - 1) with h | h
        · exact h
        · exfalso
          have hte : t = C.length - 1 := by omega
          refine hxp ?_
          rw [← hix, ← hpos2]
          refine gidx i _ hi (Nat.mod_lt _ hn) ?_
          rw [hte] at hteq
          rw [Nat.mod_eq_of_lt hi] at hteq
          rw [show C.length - 1 + r = r + (C.length - 1) from by omega]
          exact hteq.symm
      have htA : t < A.length := by omega
      have hval : (A[t]'htA) = x := by
        rw [hAget t htA, ← hix]
        refine gidx _ i (Nat.mod_lt _ hn) hi ?_
        rw [show t + r = r + t from by omega, hteq, Nat.mod_eq_of_lt hi]
      exact hval ▸ List.getElem_mem _
  ------------------------------------------------------------------
  -- the path P and its interior I
  ------------------------------------------------------------------
  have hPl : IsPathList G P := hP.1
  have hPpos : 0 < P.length := PathBasics.path_length_pos hPl
  have gidxP : ∀ (a b : ℕ) (ha : a < P.length) (hb : b < P.length), a = b →
      (P[a]'ha) = (P[b]'hb) := by intro a b ha hb h; subst h; rfl
  have hP0 : (P[0]'hPpos) = p₁ := PathBasics.getElem_zero_of_head? hP.2.1 hPpos
  have hPlast : (P[P.length - 1]'(by omega)) = p₃ :=
    PathBasics.getElem_last_of_getLast? hP.2.2 hPpos
  have hp13 : p₁ ≠ p₃ := by
    rw [← hpos1, ← hpos3]
    exact hshift_ne (C.length - 2) 0 (by omega) (by omega) (by omega)
  have hnadj13 : ¬ G.Adj p₁ p₃ := by
    rw [← hpos1, ← hpos3, hshift_adj (C.length - 2) 0 (by omega) (by omega)]
    rintro (h | h)
    · rw [Nat.mod_eq_of_lt (show C.length - 2 + 1 < C.length from by omega)] at h; omega
    · rw [Nat.mod_eq_of_lt (show (0 : ℕ) + 1 < C.length from by omega)] at h; omega
  have hPlen3 : 3 ≤ P.length := by
    by_contra hcon
    rcases Nat.lt_or_ge P.length 2 with h | h
    · refine hp13 ?_
      rw [← hP0, ← hPlast]
      exact gidxP 0 (P.length - 1) hPpos (by omega) (by omega)
    · have hP2 : P.length = 2 := by omega
      refine hnadj13 ?_
      rw [← hP0, ← hPlast]
      have hadj : G.Adj (P[0]'hPpos) (P[0 + 1]'(by omega)) :=
        PathBasics.path_adj_succ hPl (by omega)
      rw [gidxP (P.length - 1) (0 + 1) (by omega) (by omega) (by omega)]
      exact hadj
  obtain ⟨I, hIdef⟩ : ∃ I : List V, I = SPGT.interior P := ⟨_, rfl⟩
  have hIlen : I.length = P.length - 2 := by rw [hIdef]; exact PathBasics.interior_length P
  have hIpath : IsPathFrom G I (P[1]'(by omega)) (P[P.length - 2]'(by omega)) := by
    rw [hIdef]; exact PathGlue.isPathFrom_interior hPl hPlen3
  have hImem : ∀ x ∈ I, x ∈ F := by intro x hx; exact hPF x (hIdef ▸ hx)
  have hIidx : ∀ x ∈ I, ∃ (j : ℕ) (hj : j < P.length), 1 ≤ j ∧ j + 2 ≤ P.length ∧
      (P[j]'hj) = x := by
    intro x hx
    exact PathBasics.exists_getElem_of_mem_interior hPl (hIdef ▸ hx)
  ------------------------------------------------------------------
  -- glue: the new hole E
  ------------------------------------------------------------------
  have hdisj : ∀ x ∈ A, x ∉ I := by
    intro x hx hxI
    exact hFC x (hImem x hxI) ((hAmem x).mp hx).1
  have hcross : ∀ x ∈ A, ∀ y ∈ I,
      (G.Adj x y ↔ (x = p₁ ∧ y = (P[1]'(by omega))) ∨
        (x = p₃ ∧ y = (P[P.length - 2]'(by omega)))) := by
    intro x hx y hy
    obtain ⟨hxC, hxp2⟩ := (hAmem x).mp hx
    obtain ⟨j, hj, hj1, hj2, hjy⟩ := hIidx y hy
    constructor
    · intro hadj
      by_cases hxp1 : x = p₁
      · refine Or.inl ⟨hxp1, ?_⟩
        rw [hxp1, ← hP0, ← hjy] at hadj
        have hres := (PathBasics.path_adj_iff hPl hPpos hj).mp hadj
        rw [← hjy]
        exact gidxP j 1 hj (by omega) (by omega)
      · by_cases hxp3 : x = p₃
        · refine Or.inr ⟨hxp3, ?_⟩
          rw [hxp3, ← hPlast, ← hjy] at hadj
          have hres := (PathBasics.path_adj_iff hPl
            (show P.length - 1 < P.length from by omega) hj).mp hadj
          rw [← hjy]
          exact gidxP j (P.length - 2) hj (by omega) (by omega)
        · exact absurd hadj (fun hh =>
            hPno y (hIdef ▸ hy) x hxC hxp1 hxp2 hxp3 hh.symm)
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · rw [← hP0]; exact PathBasics.path_adj_succ hPl (by omega)
      · rw [← hPlast]
        exact (PathBasics.path_adj_iff hPl (show P.length - 1 < P.length from by omega)
          (show P.length - 2 < P.length from by omega)).mpr (Or.inr (by omega))
  obtain ⟨E, hEdef⟩ : ∃ E : List V, E = A ++ I := ⟨_, rfl⟩
  have hElen : E.length = (C.length - 1) + I.length := by
    rw [hEdef]; simp only [List.length_append, hAlen]
  have hIpos : 1 ≤ I.length := by omega
  have hEhole : IsHoleList G E := by
    rw [hEdef]
    exact PathGlue.glue_hole hApath hIpath hdisj hcross (by omega)
  have hmodeqE : ∀ a b : ℕ, a = b → a % E.length = b % E.length := by
    intro a b h; rw [h]
  have hEget1 : ∀ (t : ℕ) (ht : t < E.length), t < C.length - 1 →
      (E[t]'ht) = C[(t + r) % C.length]'(Nat.mod_lt _ hn) := by
    subst hEdef
    intro t ht ht2
    rw [List.getElem_append_left (by omega)]
    exact hAget t (by omega)
  have hEget2 : ∀ (t : ℕ) (ht : t < E.length), C.length - 1 ≤ t → (E[t]'ht) ∈ I := by
    subst hEdef
    intro t ht ht2
    rw [List.getElem_append_right (by omega)]
    exact List.getElem_mem _
  have hEmemY : ∀ v ∈ E, v ∉ Y := by
    intro v hv
    rw [hEdef] at hv
    rcases List.mem_append.mp hv with h | h
    · exact hCY v ((hAmem v).mp h).1
    · exact hFY v (hImem v h)
  ------------------------------------------------------------------
  -- Y-complete positions of E
  ------------------------------------------------------------------
  have hcvE1 : ∀ i : ℕ, i < C.length - 1 →
      (SegmentBasics.CycVert G Y E i ↔ SegmentBasics.CycVert G Y C (i + r)) := by
    intro i hi
    have hiE : i < E.length := by omega
    have hgetE : E[i % E.length]? = C[(i + r) % C.length]? := by
      rw [Nat.mod_eq_of_lt hiE, List.getElem?_eq_getElem hiE, hEget1 i hiE hi,
        List.getElem?_eq_getElem (Nat.mod_lt _ hn)]
    simp only [SegmentBasics.CycVert, hgetE]
  have hcvE2 : ∀ i : ℕ, C.length - 1 ≤ i → i < E.length →
      ¬ SegmentBasics.CycVert G Y E i := by
    rintro i hi1 hi2 ⟨u, hu, huY⟩
    rw [Nat.mod_eq_of_lt hi2, List.getElem?_eq_getElem hi2] at hu
    have hue : u = (E[i]'hi2) := (Option.some_inj.mp hu).symm
    exact hFnc u (hImem u (hue ▸ hEget2 i hi2 hi1)) huY
  ------------------------------------------------------------------
  -- transferring a run of C (shifted frame) to a run of E
  ------------------------------------------------------------------
  have hrun_transfer : ∀ σ Λ : ℕ, 1 ≤ Λ → σ + Λ ≤ C.length - 1 →
      (∀ t < Λ, SegmentBasics.CycVert G Y C (σ + t + r)) →
      (σ + Λ < C.length - 1 → ¬ SegmentBasics.CycVert G Y C (σ + Λ + r)) →
      (1 ≤ σ → ¬ SegmentBasics.CycVert G Y C (σ - 1 + r)) →
      ((∀ t < Λ, SegmentBasics.CycVert G Y E (σ + t)) ∧
        ¬ SegmentBasics.CycVert G Y E (σ + Λ) ∧
        ¬ SegmentBasics.CycVert G Y E (σ + (E.length - 1))) := by
    intro σ Λ hΛ1 hend hall hnext hprev
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      exact (hcvE1 (σ + t) (by omega)).mpr (hall t ht)
    · rcases Nat.lt_or_ge (σ + Λ) (C.length - 1) with h | h
      · exact fun hcon => hnext h ((hcvE1 (σ + Λ) h).mp hcon)
      · have he : σ + Λ = C.length - 1 := by omega
        rw [he]
        exact hcvE2 (C.length - 1) (by omega) (by omega)
    · rcases Nat.eq_zero_or_pos σ with rfl | hσ
      · rw [Nat.zero_add]
        exact hcvE2 (E.length - 1) (by omega) (by omega)
      · intro hcon
        refine hprev hσ ((hcvE1 (σ - 1) (by omega)).mp ?_)
        refine (SegmentBasics.cycVert_congr (C := E)
          (a := σ + (E.length - 1)) (b := σ - 1) ?_).mp hcon
        rw [show σ + (E.length - 1) = (σ - 1) + E.length from by omega, Nat.add_mod_right]
  ------------------------------------------------------------------
  -- the even run of E
  ------------------------------------------------------------------
  obtain ⟨k, L, hL2, hLeven, hLn, hallC, hnextC, hprevC⟩ := exists_even_run hBerge hodd
  obtain ⟨s, hs, hseq⟩ : ∃ s, s < C.length ∧ (s + r) % C.length = k % C.length := by
    obtain ⟨t, ht, hteq⟩ := OddWheelParityFacts.exists_offset hn r k
    exact ⟨t, ht, by rw [show t + r = r + t from by omega]; exact hteq⟩
  have hshiftall : ∀ t : ℕ, (SegmentBasics.CycVert G Y C (s + t + r) ↔
      SegmentBasics.CycVert G Y C (k + t)) := by
    intro t
    refine SegmentBasics.cycVert_congr ?_
    rw [show s + t + r = s + r + t from by omega]
    exact SegmentBasics.add_mod_congr hseq t
  have hprevS : 1 ≤ s → ¬ SegmentBasics.CycVert G Y C (s - 1 + r) := by
    intro hσ hc
    refine hprevC ((SegmentBasics.cycVert_congr
      (a := s - 1 + r) (b := k + (C.length - 1)) ?_).mp hc)
    have e := SegmentBasics.add_mod_congr hseq (C.length - 1)
    rw [← e, show s + r + (C.length - 1) = (s - 1 + r) + C.length from by omega,
      Nat.add_mod_right]
  obtain ⟨σ, Λ, hΛ2, hΛeven, hΛend, hEall, hEnext, hEprev⟩ :
      ∃ σ Λ : ℕ, 2 ≤ Λ ∧ Even Λ ∧ σ + Λ ≤ C.length - 1 ∧
        (∀ t < Λ, SegmentBasics.CycVert G Y E (σ + t)) ∧
        ¬ SegmentBasics.CycVert G Y E (σ + Λ) ∧
        ¬ SegmentBasics.CycVert G Y E (σ + (E.length - 1)) := by
    rcases Nat.lt_or_ge (C.length - 1) (s + L) with hcase | hcase
    · -- the run runs over the deleted vertex p₂
      have hs2 : s ≤ C.length - 2 := by
        rcases Nat.lt_or_ge s (C.length - 1) with h | h
        · omega
        · exfalso
          have hse : s = C.length - 1 := by omega
          refine hprevS (by omega) ?_
          rw [hse]
          exact (SegmentBasics.cycVert_congr
            (hmodeq (C.length - 2 + r) (C.length - 1 - 1 + r) (by omega))).mp hcvp1
      obtain ⟨t₀, ht₀def⟩ : ∃ t₀ : ℕ, t₀ = C.length - 1 - s := ⟨_, rfl⟩
      have ht₀1 : 1 ≤ t₀ := by omega
      have ht₀L : t₀ < L := by omega
      have ht₀L2 : t₀ + 1 < L := by
        rcases Nat.lt_or_ge (t₀ + 1) L with h | h
        · exact h
        · exfalso
          have hLe : L = t₀ + 1 := by omega
          refine hnextC ((hshiftall L).mp ?_)
          rw [show s + L + r = C.length + (0 + r) from by omega]
          exact (SegmentBasics.cycVert_congr
            (a := 0 + r) (b := C.length + (0 + r)) (by rw [Nat.add_mod_left])).mp hcvp3
      have hA : ∀ t < t₀, SegmentBasics.CycVert G Y C (s + t + r) := fun t ht =>
        (hshiftall t).mpr (hallC t (by omega))
      have hB : ∀ t < L - t₀ - 1, SegmentBasics.CycVert G Y C (0 + t + r) := by
        intro t ht
        have hstep := (hshiftall (t₀ + 1 + t)).mpr (hallC (t₀ + 1 + t) (by omega))
        refine (SegmentBasics.cycVert_congr
          (a := s + (t₀ + 1 + t) + r) (b := 0 + t + r) ?_).mp hstep
        rw [show s + (t₀ + 1 + t) + r = C.length + (0 + t + r) from by omega, Nat.add_mod_left]
      have hBnext : (0 : ℕ) + (L - t₀ - 1) < C.length - 1 →
          ¬ SegmentBasics.CycVert G Y C (0 + (L - t₀ - 1) + r) := by
        intro _ hc
        refine hnextC ((hshiftall L).mp ?_)
        refine (SegmentBasics.cycVert_congr
          (a := 0 + (L - t₀ - 1) + r) (b := s + L + r) ?_).mp hc
        rw [show s + L + r = C.length + (0 + (L - t₀ - 1) + r) from by omega, Nat.add_mod_left]
      rcases Nat.even_or_odd t₀ with hev | hod
      · obtain ⟨w, hw⟩ := hev
        obtain ⟨hA1, hA2, hA3⟩ := hrun_transfer s t₀ (by omega) (by omega) hA
          (fun h => absurd h (by omega)) hprevS
        exact ⟨s, t₀, by omega, ⟨w, hw⟩, by omega, hA1, hA2, hA3⟩
      · obtain ⟨f, hf⟩ := hod
        obtain ⟨e, he⟩ := hLeven
        obtain ⟨hB1, hB2, hB3⟩ := hrun_transfer 0 (L - t₀ - 1) (by omega) (by omega) hB
          hBnext (fun h => absurd h (by omega))
        exact ⟨0, L - t₀ - 1, by omega, ⟨(L - t₀ - 1) / 2, by omega⟩, by omega, hB1, hB2, hB3⟩
    · -- the run avoids the deleted vertex
      obtain ⟨e, he⟩ := hLeven
      obtain ⟨hA1, hA2, hA3⟩ := hrun_transfer s L (by omega) (by omega)
        (fun t ht => (hshiftall t).mpr (hallC t ht))
        (fun _ hcon => hnextC ((hshiftall L).mp hcon)) hprevS
      exact ⟨s, L, by omega, ⟨e, he⟩, by omega, hA1, hA2, hA3⟩
  ------------------------------------------------------------------
  -- (E,Y) has an odd segment
  ------------------------------------------------------------------
  have hΛE : Λ + 1 ≤ E.length := by omega
  have hseg : IsSegment G E Y ((E.rotate σ).take Λ) :=
    SegmentBasics.isSegment_of_run hEhole (by omega) hΛE hEall hEnext hEprev
  have hseglen : ((E.rotate σ).take Λ).length = Λ := by
    simp only [List.length_take, List.length_rotate]; omega
  have hsegodd : Odd (pathLength ((E.rotate σ).take Λ)) := by
    rw [SegmentBasics.odd_pathLength_iff_even_length (by omega), hseglen]
    exact hΛeven
  ------------------------------------------------------------------
  -- the edge count drops by exactly two
  ------------------------------------------------------------------
  have hceE : ∀ i : ℕ, i < C.length - 2 →
      (WheelParity.CycEdge G Y E i ↔ WheelParity.CycEdge G Y C (r + i)) := by
    intro i hi
    rw [YEdgeConfiguration.cycEdge_iff hEhole, YEdgeConfiguration.cycEdge_iff hC,
      hcvE1 i (by omega), hcvE1 (i + 1) (by omega),
      SegmentBasics.cycVert_congr (a := i + r) (b := r + i) (hmodeq (i + r) (r + i) (by omega)),
      SegmentBasics.cycVert_congr (a := i + 1 + r) (b := r + i + 1)
        (hmodeq (i + 1 + r) (r + i + 1) (by omega))]
  have hnoceE : ∀ t : ℕ, C.length - 2 + t < E.length →
      ¬ WheelParity.CycEdge G Y E (C.length - 2 + t) := by
    intro t ht hce
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · refine hcvE2 (C.length - 1) (by omega) (by omega) ?_
      refine (SegmentBasics.cycVert_congr (C := E)
        (a := C.length - 2 + 0 + 1) (b := C.length - 1)
        (hmodeqE (C.length - 2 + 0 + 1) (C.length - 1) (by omega))).mp ?_
      exact YEdgeConfiguration.cycVert_succ_of_cycEdge hEhole hce
    · exact hcvE2 (C.length - 2 + t) (by omega) (by omega)
        (YEdgeConfiguration.cycVert_of_cycEdge hEhole hce)
  have hEcount : WheelParity.cycCount G Y E E.length
      = WheelParity.cycCount G Y E (C.length - 2) := by
    have hsplit := WheelParity.cycCount_add (G := G) (Y := Y) (C := E)
      (C.length - 2) (E.length - (C.length - 2))
    rw [show C.length - 2 + (E.length - (C.length - 2)) = E.length from by omega] at hsplit
    have hz : ∑ t ∈ Finset.range (E.length - (C.length - 2)),
        (if WheelParity.CycEdge G Y E (C.length - 2 + t) then 1 else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro t ht
      rw [Finset.mem_range] at ht
      exact if_neg (hnoceE t (by omega))
    rw [hsplit, hz, Nat.add_zero]
  have hCcount : WheelParity.cycCount G Y C (r + (C.length - 2))
      = WheelParity.cycCount G Y C r + WheelParity.cycCount G Y E (C.length - 2) := by
    have h1 := WheelParity.cycCount_add (G := G) (Y := Y) (C := C) r (C.length - 2)
    have h2 := WheelParity.cycCount_eq_sum (G := G) (Y := Y) (C := E) (C.length - 2)
    have h3 : ∑ t ∈ Finset.range (C.length - 2),
        (if WheelParity.CycEdge G Y C (r + t) then 1 else 0)
        = ∑ t ∈ Finset.range (C.length - 2),
          (if WheelParity.CycEdge G Y E t then 1 else 0) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Finset.mem_range] at hi
      by_cases hce : WheelParity.CycEdge G Y E i
      · rw [if_pos hce, if_pos ((hceE i hi).mp hce)]
      · rw [if_neg hce, if_neg (fun h => hce ((hceE i hi).mpr h))]
    rw [h1, h3, ← h2]
  have hedge1 : WheelParity.CycEdge G Y C (r + (C.length - 2)) := by
    refine (YEdgeConfiguration.cycEdge_iff hC).mpr ⟨?_, ?_⟩
    · exact (SegmentBasics.cycVert_congr
        (hmodeq (C.length - 2 + r) (r + (C.length - 2)) (by omega))).mp hcvp1
    · exact (SegmentBasics.cycVert_congr
        (hmodeq (C.length - 1 + r) (r + (C.length - 2) + 1) (by omega))).mp hcvp2
  have hedge2 : WheelParity.CycEdge G Y C (r + (C.length - 2) + 1) := by
    refine (YEdgeConfiguration.cycEdge_iff hC).mpr ⟨?_, ?_⟩
    · exact (SegmentBasics.cycVert_congr
        (hmodeq (C.length - 1 + r) (r + (C.length - 2) + 1) (by omega))).mp hcvp2
    · refine (SegmentBasics.cycVert_congr
        (a := 0 + r) (b := r + (C.length - 2) + 1 + 1) ?_).mp hcvp3
      rw [show r + (C.length - 2) + 1 + 1 = (0 + r) + C.length from by omega, Nat.add_mod_right]
  have hCtot : WheelParity.cycCount G Y C (r + C.length)
      = WheelParity.cycCount G Y C r + WheelParity.cycCount G Y C C.length :=
    WheelParity.cycCount_add_length r
  have hCstep : WheelParity.cycCount G Y C (r + C.length)
      = WheelParity.cycCount G Y C (r + (C.length - 2)) + 2 := by
    have s1 : WheelParity.cycCount G Y C (r + (C.length - 2) + 1)
        = WheelParity.cycCount G Y C (r + (C.length - 2)) + 1 := by
      rw [WheelParity.cycCount_succ, if_pos hedge1]
    have s2 : WheelParity.cycCount G Y C (r + (C.length - 2) + 1 + 1)
        = WheelParity.cycCount G Y C (r + (C.length - 2) + 1) + 1 := by
      rw [WheelParity.cycCount_succ, if_pos hedge2]
    rw [show r + C.length = r + (C.length - 2) + 1 + 1 from by omega, s2, s1]
  have hkeycount : WheelParity.cycCount G Y C C.length
      = WheelParity.cycCount G Y E E.length + 2 := by omega
  ------------------------------------------------------------------
  -- two disjoint Y-complete edges of E
  ------------------------------------------------------------------
  have hEeven : Even (WheelParity.cycCount G Y E E.length) := by
    obtain ⟨f, hf⟩ := heven
    exact ⟨(WheelParity.cycCount G Y E E.length) / 2, by omega⟩
  have hrunc : WheelParity.cycCount G Y E (σ + Λ)
      = WheelParity.cycCount G Y E σ + (Λ - 1) :=
    OddWheelParityFacts.cycCount_run hEhole hEall hEnext
  have htotc : WheelParity.cycCount G Y E (σ + E.length)
      = WheelParity.cycCount G Y E σ + WheelParity.cycCount G Y E E.length :=
    WheelParity.cycCount_add_length σ
  have htailc := WheelParity.cycCount_add (G := G) (Y := Y) (C := E) (σ + Λ) (E.length - Λ)
  rw [show σ + Λ + (E.length - Λ) = σ + E.length from by omega, htotc, hrunc] at htailc
  have hsumpos : ∑ t ∈ Finset.range (E.length - Λ),
      (if WheelParity.CycEdge G Y E (σ + Λ + t) then 1 else 0) ≠ 0 := by
    obtain ⟨f, hf⟩ := hEeven
    obtain ⟨g, hg⟩ := hΛeven
    omega
  obtain ⟨t, htmem, htne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumpos
  rw [Finset.mem_range] at htmem
  have htce : WheelParity.CycEdge G Y E (σ + Λ + t) := by
    by_contra hcon
    rw [if_neg hcon] at htne
    exact htne rfl
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · exact absurd (YEdgeConfiguration.cycVert_of_cycEdge hEhole htce) hEnext
    · exact h
  have ht2 : t + 1 < E.length - Λ := by
    rcases Nat.lt_or_ge (t + 1) (E.length - Λ) with h | h
    · exact h
    · exfalso
      have hte : t = E.length - Λ - 1 := by omega
      refine hEprev ?_
      have hcv := YEdgeConfiguration.cycVert_of_cycEdge hEhole htce
      rwa [show σ + Λ + t = σ + (E.length - 1) from by omega] at hcv
  ------------------------------------------------------------------
  -- (E, Y) is an odd wheel
  ------------------------------------------------------------------
  have hEpos : 0 < E.length := by omega
  have hcyc0 : WheelParity.CycEdge G Y E σ :=
    (YEdgeConfiguration.cycEdge_iff hEhole).mpr ⟨hEall 0 (by omega), hEall 1 (by omega)⟩
  have htce' : WheelParity.CycEdge G Y E (σ + (Λ + t)) := by
    rw [show σ + (Λ + t) = σ + Λ + t from by omega]; exact htce
  have hEdgeA := edgeComplete_of_cycEdge hEpos hcyc0
  have hEdgeB := edgeComplete_of_cycEdge hEpos htce'
  have hcancel : ∀ a b : ℕ, a < E.length → b < E.length →
      (σ + a) % E.length = (σ + b) % E.length → a = b := by
    intro a b ha hb h
    have h3 : a % E.length = b % E.length := mod_cancel_add_left h
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h3
  have hvne : ∀ a b : ℕ, a < E.length → b < E.length → a ≠ b →
      (E[(σ + a) % E.length]'(Nat.mod_lt _ hEpos)) ≠
        (E[(σ + b) % E.length]'(Nat.mod_lt _ hEpos)) := fun a b ha hb hab =>
    HoleBasics.hole_ne_of_ne_index hEhole _ _ (fun h => hab (hcancel a b ha hb h))
  have hEwheel : IsWheel G E Y := by
    refine ⟨⟨hEhole, by rw [holeLength]; omega⟩, ⟨hYne, hYanti, hEmemY⟩,
      E[(σ + 0) % E.length]'(Nat.mod_lt _ hEpos),
      E[(σ + 1) % E.length]'(Nat.mod_lt _ hEpos),
      E[(σ + (Λ + t)) % E.length]'(Nat.mod_lt _ hEpos),
      E[(σ + (Λ + t + 1)) % E.length]'(Nat.mod_lt _ hEpos),
      List.getElem_mem _, List.getElem_mem _, List.getElem_mem _, List.getElem_mem _,
      hEdgeA, hEdgeB,
      hvne 0 (Λ + t) (by omega) (by omega) (by omega),
      hvne 0 (Λ + t + 1) (by omega) (by omega) (by omega),
      hvne 1 (Λ + t) (by omega) (by omega) (by omega),
      hvne 1 (Λ + t + 1) (by omega) (by omega) (by omega)⟩
  have hEodd : IsOddWheel G E Y := ⟨hEwheel, _, hseg, hsegodd⟩
  have hyC : OptimalWheelChoice.yEdgeCount G Y C = WheelParity.cycCount G Y C C.length := by
    rw [OptimalWheelChoice.yEdgeCount_def]
    exact WheelParity.ncard_yEdges_eq_cycCount hC
  have hyE : OptimalWheelChoice.yEdgeCount G Y E = WheelParity.cycCount G Y E E.length := by
    rw [OptimalWheelChoice.yEdgeCount_def]
    exact WheelParity.ncard_yEdges_eq_cycCount hEhole
  have hfin := hmin E hEodd
  omega

/-- **PAPER (16.3, printed p. 101), the closing paragraph.**  Under the optimality of the odd
wheel `(C, Y)`, the third alternative of 16.2 is contradictory. -/
theorem contradiction_from_bullet_three
    (hBerge : Berge G) (hodd : IsOddWheel G C Y)
    (hmin : ∀ C', IsOddWheel G C' Y →
      OptimalWheelChoice.yEdgeCount G Y C ≤ OptimalWheelChoice.yEdgeCount G Y C')
    (F : Set V) (hFC : ∀ f ∈ F, f ∉ C) (hFY : ∀ f ∈ F, f ∉ Y)
    (hFnc : ∀ f ∈ F, ¬ VertexComplete G f Y)
    (p₁ p₂ p₃ : V) (hblock : ∃ k, [p₁,p₂,p₃] <+: C.rotate k ∨ [p₃,p₂,p₁] <+: C.rotate k)
    (h₁ : VertexComplete G p₁ Y) (h₂ : VertexComplete G p₂ Y) (h₃ : VertexComplete G p₃ Y)
    (P : List V) (hP : IsPathFrom G P p₁ p₃) (hPF : ∀ x ∈ SPGT.interior P, x ∈ F)
    (hPno : ∀ x ∈ SPGT.interior P, ∀ u ∈ C, u ≠ p₁ → u ≠ p₂ → u ≠ p₃ → ¬ G.Adj x u) :
    False := by
  obtain ⟨k, hk⟩ := hblock
  rcases hk with hk | hk
  · exact core hBerge hodd hmin F hFC hFY hFnc p₁ p₂ p₃ k hk h₁ h₂ h₃ P hP hPF hPno
  · refine core hBerge hodd hmin F hFC hFY hFnc p₃ p₂ p₁ k hk h₃ h₂ h₁ P.reverse
      (PathBasics.isPathFrom_reverse hP) ?_ ?_
    · intro x hx
      exact hPF x (PathBasics.mem_interior_reverse.mp hx)
    · intro x hx u hu hu3 hu2 hu1
      exact hPno x (PathBasics.mem_interior_reverse.mp hx) u hu hu1 hu2 hu3

end Workspace.ProofLemmas.OddWheelRebuild
