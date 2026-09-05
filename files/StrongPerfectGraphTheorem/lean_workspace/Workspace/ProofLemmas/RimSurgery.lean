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
import Workspace.ProofLemmas.OptimalWheelChoice

/-!
# Rim surgery: the hole `C'` of step (1) of 23.2

PAPER (23.2, printed p. 139), step **(1)** *"Exactly 4 edges of `C` are `Y`-complete"*, first
two sentences:

> *"For by 23.1 there is a subpath `c₁-c₂-c₃` of `C` such that `c₁, c₂, c₃` are all
> `Y`-complete, and a path `c₁-p₁-⋯-p_k-c₃` such that none of `p₁, …, p_k` are in
> `V(C) ∪ Y`, none of them is `Y`-complete, and none of them has a neighbour in
> `V(C) \ {c₁, c₂, c₃}`.  Let `C'` be the hole formed by the union of the paths `C \ c₂`,
> `c₁-p₁-⋯-p_k-c₃`.  Then it has length `≥ 6`, and it contains fewer `Y`-complete edges
> than `C`."*

`exists_rim_surgery` is exactly that construction, together with the edge count made
precise: `C'` carries **two** fewer `Y`-complete edges than `C`, namely `c₁c₂` and `c₂c₃`.

The remainder of step (1) — *"From the choice of `(C,Y)` it follows that `(C',Y)` is not a
wheel, and since `C` has at least 4 `Y`-complete edges, and `C'` has only two fewer, it
follows that exactly 4 edges of `C` are `Y`-complete"* — is left to the caller: it needs the
minimality clause of the choice of `(C,Y)`, which is not an input here.

## How the printed construction is realised

Write `n = |C|` and put the rim in the frame in which `c₃, …, c₁` occupy positions
`0, …, n-2` and the deleted vertex `c₂` occupies the missing position `n-1`; concretely,
with `r = q + 2` for the rotation `q` witnessing `[c₁,c₂,c₃] <+: C.rotate q`, position `i` of
the new hole is position `(i + r) mod n` of `C`.

* **`C \ c₂` is a path.**  It is the proper cyclic arc `A = (C.rotate r).take (n-1)`, a path
  from `c₃` to `c₁` by `WheelParity.arc_isPathFrom`, whose vertices are exactly the vertices
  of `C` other than `c₂`.
* **The new hole.**  `C' = A ++ P*`, assembled by `PathGlue.glue_hole`.  The cross condition
  — the only edges between `A` and `P*` are `c₁p₁` and `c₃p_k` — is exactly 23.1's *"none of
  them has a neighbour in `V(C) \ {c₁,c₂,c₃}`"* plus inducedness of `P`.
  `|C'| = (n-1) + |P*| ≥ 6`, since `|P*| ≥ 1` (`c₁` and `c₃` are at cyclic distance `2` on
  the induced hole `C`, hence nonadjacent, so `P` has at least three vertices).
* **The `Y`-complete vertices of `C'`** are those of `C` except `c₂`: no `pᵢ` is
  `Y`-complete.  That is `cvE1`/`cvE2` inside the proof, the two bridge lemmas of the
  analogous 16.3 surgery in `ProofLemmas.OddWheelRebuild`.
* **The count.**  The `Y`-complete cyclic edges of `C'` are the `Y`-complete cyclic edges of
  `C` other than `c₁c₂` and `c₂c₃`, so `yEdgeCount G Y C = yEdgeCount G Y C' + 2`.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Workspace.ProofLemmas.RimSurgery

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {C : List V} {Y : Set V}

private theorem mod_cancel_add_right {n a b c : ℕ} (h : (a + c) % n = (b + c) % n) :
    a % n = b % n := Nat.ModEq.add_right_cancel' c h

/-- The surgery of step (1) of 23.2, with the three cyclically consecutive `Y`-complete
vertices given by a concrete rotation `q`. -/
private theorem core
    (hC : IsHoleList G C) (hn6 : 6 ≤ C.length) (hCY : ∀ v ∈ C, v ∉ Y)
    (c₁ c₂ c₃ : V) (q : ℕ) (hblock : [c₁, c₂, c₃] <+: C.rotate q)
    (h₁ : VertexComplete G c₁ Y) (h₂ : VertexComplete G c₂ Y) (h₃ : VertexComplete G c₃ Y)
    (P : List V) (hP : IsPathFrom G P c₁ c₃)
    (hPC : ∀ w ∈ SPGT.interior P, w ∉ C)
    (hPY : ∀ w ∈ SPGT.interior P, w ∉ Y)
    (hPnc : ∀ w ∈ SPGT.interior P, ¬ VertexComplete G w Y)
    (hPno : ∀ w ∈ SPGT.interior P, ∀ c ∈ C, c ≠ c₁ → c ≠ c₂ → c ≠ c₃ → ¬ G.Adj w c) :
    ∃ C' : List V, IsHoleList G C' ∧ 6 ≤ holeLength C' ∧ (∀ v ∈ C', v ∉ Y) ∧
      (∀ v : V, v ∈ C' ↔ ((v ∈ C ∧ v ≠ c₂) ∨ v ∈ SPGT.interior P)) ∧
      OptimalWheelChoice.yEdgeCount G Y C = OptimalWheelChoice.yEdgeCount G Y C' + 2 := by
  classical
  have hn : 0 < C.length := by omega
  have hnd : C.Nodup := hC.2.1
  have gidx : ∀ (a b : ℕ) (ha : a < C.length) (hb : b < C.length), a = b →
      (C[a]'ha) = (C[b]'hb) := by intro a b ha hb h; subst h; rfl
  have hmodeq : ∀ a b : ℕ, a = b → a % C.length = b % C.length := by
    intro a b h; rw [h]
  ------------------------------------------------------------------
  -- the positions of c₁, c₂, c₃ on the rim
  ------------------------------------------------------------------
  have hrlen : (C.rotate q).length = C.length := by simp
  have hr0 : (0 : ℕ) < (C.rotate q).length := by omega
  have hr1 : (1 : ℕ) < (C.rotate q).length := by omega
  have hr2 : (2 : ℕ) < (C.rotate q).length := by omega
  have hq0 : ((C.rotate q)[0]'hr0) = c₁ := by
    simpa using (hblock.getElem (i := 0) (by simp)).symm
  have hq1 : ((C.rotate q)[1]'hr1) = c₂ := by
    simpa using (hblock.getElem (i := 1) (by simp)).symm
  have hq2 : ((C.rotate q)[2]'hr2) = c₃ := by
    simpa using (hblock.getElem (i := 2) (by simp)).symm
  have hc0 : (C[(0 + q) % C.length]'(Nat.mod_lt _ hn)) = c₁ :=
    (WheelParity.getElem_rotate_eq hn hr0).symm.trans hq0
  have hc1 : (C[(1 + q) % C.length]'(Nat.mod_lt _ hn)) = c₂ :=
    (WheelParity.getElem_rotate_eq hn hr1).symm.trans hq1
  have hc2 : (C[(2 + q) % C.length]'(Nat.mod_lt _ hn)) = c₃ :=
    (WheelParity.getElem_rotate_eq hn hr2).symm.trans hq2
  obtain ⟨r, hrdef⟩ : ∃ r : ℕ, r = q + 2 := ⟨_, rfl⟩
  have hpos3 : (C[(0 + r) % C.length]'(Nat.mod_lt _ hn)) = c₃ :=
    (gidx _ _ (Nat.mod_lt _ hn) (Nat.mod_lt _ hn)
      (hmodeq (0 + r) (2 + q) (by omega))).trans hc2
  have hpos1 : (C[(C.length - 2 + r) % C.length]'(Nat.mod_lt _ hn)) = c₁ := by
    refine Eq.trans (gidx _ _ (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) ?_) hc0
    rw [hrdef, show C.length - 2 + (q + 2) = C.length + (0 + q) from by omega, Nat.add_mod_left]
  have hpos2 : (C[(C.length - 1 + r) % C.length]'(Nat.mod_lt _ hn)) = c₂ := by
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
  -- the arc  A = C minus c₂
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
  have hApath : IsPathFrom G A c₃ c₁ := by
    rw [← hpos3, ← hpos1, hAdef]
    exact WheelParity.arc_isPathFrom hC (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) (by omega) (by omega)
      (hmodeq r (0 + r) (by omega)) (hmodeq (r + (C.length - 1) - 1) (C.length - 2 + r) (by omega))
  have hAmem : ∀ x : V, x ∈ A ↔ (x ∈ C ∧ x ≠ c₂) := by
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
  have hP0 : (P[0]'hPpos) = c₁ := PathBasics.getElem_zero_of_head? hP.2.1 hPpos
  have hPlast : (P[P.length - 1]'(by omega)) = c₃ :=
    PathBasics.getElem_last_of_getLast? hP.2.2 hPpos
  have hp13 : c₁ ≠ c₃ := by
    rw [← hpos1, ← hpos3]
    exact hshift_ne (C.length - 2) 0 (by omega) (by omega) (by omega)
  have hnadj13 : ¬ G.Adj c₁ c₃ := by
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
  have hIC : ∀ x ∈ I, x ∉ C := fun x hx => hPC x (hIdef ▸ hx)
  have hIY : ∀ x ∈ I, x ∉ Y := fun x hx => hPY x (hIdef ▸ hx)
  have hInc : ∀ x ∈ I, ¬ VertexComplete G x Y := fun x hx => hPnc x (hIdef ▸ hx)
  have hIidx : ∀ x ∈ I, ∃ (j : ℕ) (hj : j < P.length), 1 ≤ j ∧ j + 2 ≤ P.length ∧
      (P[j]'hj) = x := by
    intro x hx
    exact PathBasics.exists_getElem_of_mem_interior hPl (hIdef ▸ hx)
  ------------------------------------------------------------------
  -- glue: the new hole E
  ------------------------------------------------------------------
  have hdisj : ∀ x ∈ A, x ∉ I := by
    intro x hx hxI
    exact hIC x hxI ((hAmem x).mp hx).1
  have hcross : ∀ x ∈ A, ∀ y ∈ I,
      (G.Adj x y ↔ (x = c₁ ∧ y = (P[1]'(by omega))) ∨
        (x = c₃ ∧ y = (P[P.length - 2]'(by omega)))) := by
    intro x hx y hy
    obtain ⟨hxC, hxp2⟩ := (hAmem x).mp hx
    obtain ⟨j, hj, hj1, hj2, hjy⟩ := hIidx y hy
    constructor
    · intro hadj
      by_cases hxp1 : x = c₁
      · refine Or.inl ⟨hxp1, ?_⟩
        rw [hxp1, ← hP0, ← hjy] at hadj
        have hres := (PathBasics.path_adj_iff hPl hPpos hj).mp hadj
        rw [← hjy]
        exact gidxP j 1 hj (by omega) (by omega)
      · by_cases hxp3 : x = c₃
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
  have hEmem : ∀ x : V, x ∈ E ↔ ((x ∈ C ∧ x ≠ c₂) ∨ x ∈ SPGT.interior P) := by
    intro x
    rw [hEdef, List.mem_append, hAmem x, hIdef]
  have hEmemY : ∀ v ∈ E, v ∉ Y := by
    intro v hv
    rw [hEdef] at hv
    rcases List.mem_append.mp hv with h | h
    · exact hCY v ((hAmem v).mp h).1
    · exact hIY v h
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
    exact hInc u (hue ▸ hEget2 i hi2 hi1) huY
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
  -- package
  ------------------------------------------------------------------
  have hyC : OptimalWheelChoice.yEdgeCount G Y C = WheelParity.cycCount G Y C C.length := by
    rw [OptimalWheelChoice.yEdgeCount_def]
    exact WheelParity.ncard_yEdges_eq_cycCount hC
  have hyE : OptimalWheelChoice.yEdgeCount G Y E = WheelParity.cycCount G Y E E.length := by
    rw [OptimalWheelChoice.yEdgeCount_def]
    exact WheelParity.ncard_yEdges_eq_cycCount hEhole
  exact ⟨E, hEhole, by rw [holeLength]; omega, hEmemY, hEmem, by omega⟩

/-- **PAPER (23.2, printed p. 139), step (1), the surgery.**

> *"Let `C'` be the hole formed by the union of the paths `C \ c₂`, `c₁-p₁-⋯-p_k-c₃`.  Then
> it has length `≥ 6`, and it contains fewer `Y`-complete edges than `C`."*

The hypotheses are exactly the conclusion of `thm_23_1` (23.1) together with the three
clauses of `IsWheel G C Y` that the construction consumes (`C` is a hole of length `≥ 6`
disjoint from `Y`).  The conclusion pins down `C'` completely: it is a hole of length `≥ 6`
disjoint from `Y`, its vertex set is `(V(C) \ {c₂}) ∪ {p₁, …, p_k}`, and it carries exactly
two fewer `Y`-complete edges than `C` — the two lost edges being `c₁c₂` and `c₂c₃`. -/
theorem exists_rim_surgery
    (hC : IsHoleList G C) (hn6 : 6 ≤ holeLength C) (hCY : ∀ v ∈ C, v ∉ Y)
    (c₁ c₂ c₃ : V) (P : List V)
    (hblock : ∃ k : ℕ, [c₁, c₂, c₃] <+: C.rotate k)
    (h₁ : VertexComplete G c₁ Y) (h₂ : VertexComplete G c₂ Y) (h₃ : VertexComplete G c₃ Y)
    (hP : IsPathFrom G P c₁ c₃)
    (hPCY : ∀ w ∈ SPGT.interior P, w ∉ C ∧ w ∉ Y)
    (hPnc : ∀ w ∈ SPGT.interior P, ¬ VertexComplete G w Y)
    (hPno : ∀ w ∈ SPGT.interior P, ∀ c ∈ C, c ≠ c₁ → c ≠ c₂ → c ≠ c₃ → ¬ G.Adj w c) :
    ∃ C' : List V,
      IsHoleList G C' ∧
      6 ≤ holeLength C' ∧
      (∀ v ∈ C', v ∉ Y) ∧
      (∀ v : V, v ∈ C' ↔ ((v ∈ C ∧ v ≠ c₂) ∨ v ∈ SPGT.interior P)) ∧
      OptimalWheelChoice.yEdgeCount G Y C = OptimalWheelChoice.yEdgeCount G Y C' + 2 ∧
      OptimalWheelChoice.yEdgeCount G Y C'
        = OptimalWheelChoice.yEdgeCount G Y C - 2 := by
  obtain ⟨k, hk⟩ := hblock
  obtain ⟨C', hhole, hlen, hY, hmem, hcount⟩ :=
    core hC (by rw [holeLength] at hn6; exact hn6) hCY c₁ c₂ c₃ k hk h₁ h₂ h₃ P hP
      (fun w hw => (hPCY w hw).1) (fun w hw => (hPCY w hw).2) hPnc hPno
  exact ⟨C', hhole, hlen, hY, hmem, hcount, by omega⟩

/-- The same, with the ambient wheel packaged as `IsWheel G C Y` — the form the proof of 23.2
holds it in. -/
theorem exists_rim_surgery_of_wheel
    (hw : IsWheel G C Y)
    (c₁ c₂ c₃ : V) (P : List V)
    (hblock : ∃ k : ℕ, [c₁, c₂, c₃] <+: C.rotate k)
    (h₁ : VertexComplete G c₁ Y) (h₂ : VertexComplete G c₂ Y) (h₃ : VertexComplete G c₃ Y)
    (hP : IsPathFrom G P c₁ c₃)
    (hPCY : ∀ w ∈ SPGT.interior P, w ∉ C ∧ w ∉ Y)
    (hPnc : ∀ w ∈ SPGT.interior P, ¬ VertexComplete G w Y)
    (hPno : ∀ w ∈ SPGT.interior P, ∀ c ∈ C, c ≠ c₁ → c ≠ c₂ → c ≠ c₃ → ¬ G.Adj w c) :
    ∃ C' : List V,
      IsHoleList G C' ∧
      6 ≤ holeLength C' ∧
      (∀ v ∈ C', v ∉ Y) ∧
      (∀ v : V, v ∈ C' ↔ ((v ∈ C ∧ v ≠ c₂) ∨ v ∈ SPGT.interior P)) ∧
      OptimalWheelChoice.yEdgeCount G Y C = OptimalWheelChoice.yEdgeCount G Y C' + 2 ∧
      OptimalWheelChoice.yEdgeCount G Y C'
        = OptimalWheelChoice.yEdgeCount G Y C - 2 :=
  exists_rim_surgery hw.1.1 hw.1.2 hw.2.1.2.2 c₁ c₂ c₃ P hblock h₁ h₂ h₃ hP hPCY hPnc hPno

end Workspace.ProofLemmas.RimSurgery
