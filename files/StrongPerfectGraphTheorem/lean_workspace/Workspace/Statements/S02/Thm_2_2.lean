/-  Proof attempt for statement 2.2 of Chudnovsky-Robertson-Seymour-Thomas,
    *The Strong Perfect Graph Theorem*.  Reproduces the printed proof
    (`paper/proofs/2_2.md`, printed p. 9) step for step. -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.Statements.S02.Thm_2_1
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics

-- `[Fintype V]` and `[DecidableEq V]` come from the frozen statement's `variable` line
-- and are not used by the proof; the linter would otherwise flag them.
set_option linter.unusedSectionVars false

namespace Workspace.Statements.S02

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas

namespace SPGT

/-! ### Generic helpers used by the proof of 2.2 -/

section Helpers

variable {V : Type*}

/-- A list of at least four distinct vertices whose adjacencies are the cyclically
consecutive pairs *for indices `i ≤ j`* is a hole: the remaining pairs follow by
symmetry of adjacency. -/
private theorem isHoleList_of_le {G : SimpleGraph V} {l : List V}
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
consecutive means `j = i + 1` or (the wrap-around) `i = 0` and `j = n`. -/
private theorem cyc_rhs {n i j : ℕ} (hn : 1 ≤ n) (hi : i ≤ n) (hj : j ≤ n) (hij : i ≤ j) :
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

/-- A list of length four is a four-element literal. -/
private theorem length_eq_four {α : Type*} {l : List α} (h : l.length = 4) :
    ∃ a b c d, l = [a, b, c, d] := by
  match l, h with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

end Helpers

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **2.2** (printed p. 8)

PAPER: *"Let `G` be Berge, let `X` be an anticonnected subset of `V(G)`, and `P`
be a path in `G \ X` with odd length, such that both ends of `P` are
`X`-complete, and no edge of `P` is `X`-complete.  Then every `X`-complete vertex
of `G` has a neighbour in `P*`."* -/
theorem thm_2_2 (G : SimpleGraph V) (hG : Berge G) (X : Set V)
    (hX : AnticonnectedSet G X) (p : List V) (p₁ pn : V)
    (hp : IsPathFrom G p p₁ pn) (hpX : ∀ w ∈ p, w ∉ X)
    (hodd : Odd (pathLength p))
    (hp₁ : VertexComplete G p₁ X) (hpn : VertexComplete G pn X)
    (hnoedge : ¬ ∃ u ∈ p, ∃ v ∈ p, EdgeComplete G X u v) :
    ∀ v : V, VertexComplete G v X → ∃ w ∈ SPGT.interior p, G.Adj v w := by
  -- PAPER: *"Let `v` be `X`-complete."*
  intro v hvX
  have hvnX : v ∉ X := fun hv => G.irrefl (hvX v hv)
  have hpl : IsPathList G p := hp.1
  have hnpos : 0 < p.length := PathBasics.path_length_pos hpl
  have hp0 : p[0]'hnpos = p₁ := PathBasics.getElem_zero_of_head? hp.2.1 hnpos
  have hplast : p[p.length - 1]'(by omega) = pn :=
    PathBasics.getElem_last_of_getLast? hp.2.2 hnpos
  -- PAPER: *"Certainly `P` has length `> 1`, since its ends are `X`-complete and
  -- therefore nonadjacent."*  Were the two ends adjacent, that edge of `P` would be
  -- an `X`-complete edge of `P`, contrary to hypothesis.
  have hlen1 : pathLength p ≠ 1 := by
    intro h1
    exact hnoedge ⟨p₁, (PathBasics.isPathFrom_ends_mem hp).1, pn,
      (PathBasics.isPathFrom_ends_mem hp).2,
      PathBasics.isPathFrom_ends_adj_of_length_one hp h1, hp₁, hpn⟩
  have hge3 : 3 ≤ pathLength p := by obtain ⟨k, hk⟩ := hodd; omega
  rcases (show 5 ≤ pathLength p ∨ pathLength p = 3 by obtain ⟨k, hk⟩ := hodd; omega) with
    hcase | hcase
  -- ======================================================================
  -- PAPER: *"Suppose first it has length `> 3`.  Then by 2.1, `X` contains a
  -- leap, and so there is a path `Q` with ends in `X` and with `Q* = P*`."*
  -- ======================================================================
  · obtain hedge | ⟨-, a, ha, b, hb, hleap⟩ | ⟨h3, -⟩ :=
      thm_2_1 G hG X hX p p₁ pn hp hpX hodd hp₁ hpn
    · exact absurd hedge hnoedge
    · obtain ⟨-, -, hab, hnab, hadja, hadjb⟩ := hleap
      have hn6 : 6 ≤ p.length := by have := PathBasics.pathLength_eq p; omega
      -- PAPER: *"Then `v` is adjacent to both ends of `Q`"*
      have hva : G.Adj v a := hvX a ha
      have hvb : G.Adj v b := hvX b hb
      have hanp : a ∉ p := fun h => hpX a h ha
      have hbnp : b ∉ p := fun h => hpX b h hb
      have hvna : v ≠ a := fun h => hvnX (by rw [h]; exact ha)
      have hvnb : v ≠ b := fun h => hvnX (by rw [h]; exact hb)
      -- PAPER: *"it follows that `v` has a neighbour in `Q* = P*`"*; suppose not.
      by_contra hcon
      push Not at hcon
      have hmemint : ∀ (k : ℕ) (hk : k < p.length), 1 ≤ k → k ≤ p.length - 2 →
          (p[k]'hk) ∈ SPGT.interior p := by
        intro k hk h1 h2
        rw [PathBasics.mem_interior_iff_of_pathFrom hp]
        refine ⟨List.getElem_mem hk, ?_, ?_⟩
        · rw [← hp0]; exact PathBasics.path_ne_of_ne_index hpl hk hnpos (by omega)
        · rw [← hplast]; exact PathBasics.path_ne_of_ne_index hpl hk (by omega) (by omega)
      -- `v` is not a vertex of `P`: it is adjacent to both `a` and `b`, and the
      -- only vertices of `P` adjacent to both are the two ends, each of which has
      -- an interior neighbour.
      have hvnp : v ∉ p := by
        intro hvp
        obtain ⟨k, hk, hkv⟩ := List.mem_iff_getElem.mp hvp
        have hka : k = 0 ∨ k = 1 ∨ k = p.length - 1 :=
          (hadja k hk).mp (by rw [hkv]; exact (G.adj_comm v a).mp hva)
        have hkb : k = 0 ∨ k = p.length - 2 ∨ k = p.length - 1 :=
          (hadjb k hk).mp (by rw [hkv]; exact (G.adj_comm v b).mp hvb)
        rcases (show k = 0 ∨ k = p.length - 1 by omega) with rfl | rfl
        · refine hcon _ (hmemint 1 (by omega) (by omega) (by omega)) ?_
          have hadj : G.Adj (p[0]'hk) (p[1]'(by omega)) :=
            (PathBasics.path_adj_iff hpl hk (by omega)).mpr (Or.inl rfl)
          rwa [hkv] at hadj
        · refine hcon _ (hmemint (p.length - 2) (by omega) (by omega) (by omega)) ?_
          have hadj : G.Adj (p[p.length - 1]'hk) (p[p.length - 2]'(by omega)) :=
            (PathBasics.path_adj_iff hpl hk (by omega)).mpr (Or.inr (by omega))
          rwa [hkv] at hadj
      -- The path `Q = a-p₂-⋯-p_{n-1}-b` of the leap, extended by `v`, encoded by
      -- the index function `f` on `0,…,n`.
      obtain ⟨f, hf0, hf1, hfn, hfp⟩ : ∃ f : ℕ → V, f 0 = v ∧ f 1 = a ∧ f p.length = b ∧
          ∀ (j : ℕ), 2 ≤ j → j ≤ p.length - 1 → ∀ hj : j - 1 < p.length,
            f j = p[j - 1]'hj := by
        refine ⟨fun j => if j = 0 then v else if j = 1 then a else if j = p.length then b
          else p.getD (j - 1) v, by simp, by simp, ?_, ?_⟩
        · have h0 : p.length ≠ 0 := by omega
          have h1 : p.length ≠ 1 := by omega
          simp [h0, h1]
        · intro j h2 h3 hj
          simp only [if_neg (show ¬ (j = 0) by omega), if_neg (show ¬ (j = 1) by omega),
            if_neg (show ¬ (j = p.length) by omega)]
          exact List.getD_eq_getElem p v hj
      have hfcases : ∀ j, j ≤ p.length →
          (j = 0 ∧ f j = v) ∨ (j = 1 ∧ f j = a) ∨ (j = p.length ∧ f j = b) ∨
          (∃ hj : j - 1 < p.length, 2 ≤ j ∧ j ≤ p.length - 1 ∧ f j = p[j - 1]'hj) := by
        intro j hj
        by_cases h0 : j = 0
        · exact Or.inl ⟨h0, by rw [h0]; exact hf0⟩
        by_cases h1 : j = 1
        · exact Or.inr (Or.inl ⟨h1, by rw [h1]; exact hf1⟩)
        by_cases hn : j = p.length
        · exact Or.inr (Or.inr (Or.inl ⟨hn, by rw [hn]; exact hfn⟩))
        · exact Or.inr (Or.inr (Or.inr
            ⟨by omega, by omega, by omega, hfp j (by omega) (by omega) (by omega)⟩))
      have hfv : ∀ j, j ≤ p.length → f j = v → j = 0 := by
        intro j hj hfj
        rcases hfcases j hj with ⟨h, -⟩ | ⟨-, he⟩ | ⟨-, he⟩ | ⟨hkj, -, -, he⟩
        · exact h
        · exact absurd (he.symm.trans hfj) (Ne.symm hvna)
        · exact absurd (he.symm.trans hfj) (Ne.symm hvnb)
        · exact absurd (show v ∈ p by
            rw [← he.symm.trans hfj]; exact List.getElem_mem hkj) hvnp
      have hfa : ∀ j, j ≤ p.length → f j = a → j = 1 := by
        intro j hj hfj
        rcases hfcases j hj with ⟨-, he⟩ | ⟨h, -⟩ | ⟨-, he⟩ | ⟨hkj, -, -, he⟩
        · exact absurd (he.symm.trans hfj) hvna
        · exact h
        · exact absurd (he.symm.trans hfj) (Ne.symm hab)
        · exact absurd (show a ∈ p by
            rw [← he.symm.trans hfj]; exact List.getElem_mem hkj) hanp
      have hfb : ∀ j, j ≤ p.length → f j = b → j = p.length := by
        intro j hj hfj
        rcases hfcases j hj with ⟨-, he⟩ | ⟨-, he⟩ | ⟨h, -⟩ | ⟨hkj, -, -, he⟩
        · exact absurd (he.symm.trans hfj) hvnb
        · exact absurd (he.symm.trans hfj) hab
        · exact h
        · exact absurd (show b ∈ p by
            rw [← he.symm.trans hfj]; exact List.getElem_mem hkj) hbnp
      have hfpinv : ∀ j, j ≤ p.length → ∀ (k : ℕ) (hk : k < p.length),
          f j = (p[k]'hk) → j = k + 1 := by
        intro j hj k hk hfj
        rcases hfcases j hj with ⟨-, he⟩ | ⟨-, he⟩ | ⟨-, he⟩ | ⟨hkj, h2, -, he⟩
        · exact absurd (show v ∈ p by
            rw [he.symm.trans hfj]; exact List.getElem_mem hk) hvnp
        · exact absurd (show a ∈ p by
            rw [he.symm.trans hfj]; exact List.getElem_mem hk) hanp
        · exact absurd (show b ∈ p by
            rw [he.symm.trans hfj]; exact List.getElem_mem hk) hbnp
        · have hik : j - 1 = k := by
            by_contra hne
            exact PathBasics.path_ne_of_ne_index hpl hkj hk hne (he.symm.trans hfj)
          omega
      have hLp : ((List.range (p.length + 1)).map f).length = p.length + 1 := by simp
      have hgetp : ∀ (j : ℕ) (hj : j < ((List.range (p.length + 1)).map f).length),
          (((List.range (p.length + 1)).map f)[j]'hj) = f j := by
        intro j hj; simp
      -- PAPER: *"since `G|(V(Q) ∪ {v})` is not an odd hole"*
      have hhole : IsHoleList G ((List.range (p.length + 1)).map f) := by
        refine isHoleList_of_le (by rw [hLp]; omega) ?_ ?_
        · refine List.Nodup.map_on ?_ List.nodup_range
          intro x hx y hy hxy
          rw [List.mem_range] at hx hy
          rcases hfcases x (by omega) with ⟨h, he⟩ | ⟨h, he⟩ | ⟨h, he⟩ | ⟨hkx, h2, -, he⟩
          · rw [h, hfv y (by omega) (hxy.symm.trans he)]
          · rw [h, hfa y (by omega) (hxy.symm.trans he)]
          · rw [h, hfb y (by omega) (hxy.symm.trans he)]
          · have := hfpinv y (by omega) (x - 1) hkx (hxy.symm.trans he)
            omega
        · intro i j hi hj hle
          have hi' : i ≤ p.length := by have h := hi; rw [hLp] at h; omega
          have hj' : j ≤ p.length := by have h := hj; rw [hLp] at h; omega
          rw [hgetp i hi, hgetp j hj, hLp, cyc_rhs (by omega) hi' hj' hle]
          rcases hfcases i hi' with ⟨hi0, hfi⟩ | ⟨hi1, hfi⟩ | ⟨hin, hfi⟩ | ⟨hki, hi2, hi3, hfi⟩ <;>
            rcases hfcases j hj' with ⟨hj0, hfj⟩ | ⟨hj1, hfj⟩ | ⟨hjn, hfj⟩ | ⟨hkj, hj2, hj3, hfj⟩
          -- i = 0
          · rw [hfi, hfj]; exact iff_of_false (G.irrefl) (by omega)
          · rw [hfi, hfj]; exact iff_of_true hva (Or.inl (by omega))
          · rw [hfi, hfj]; exact iff_of_true hvb (Or.inr ⟨by omega, by omega⟩)
          · rw [hfi, hfj]
            exact iff_of_false (hcon _ (hmemint (j - 1) hkj (by omega) (by omega))) (by omega)
          -- i = 1
          · exfalso; omega
          · rw [hfi, hfj]; exact iff_of_false (G.irrefl) (by omega)
          · rw [hfi, hfj]; exact iff_of_false hnab (by omega)
          · rw [hfi, hfj, hadja (j - 1) hkj]; omega
          -- i = p.length
          · exfalso; omega
          · exfalso; omega
          · rw [hfi, hfj]; exact iff_of_false (G.irrefl) (by omega)
          · exfalso; omega
          -- 2 ≤ i ≤ p.length - 1
          · exfalso; omega
          · exfalso; omega
          · rw [hfi, hfj, G.adj_comm, hadjb (i - 1) hki]; omega
          · rw [hfi, hfj, PathBasics.path_adj_iff hpl hki hkj]; omega
      have hfin := hG.1 _ hhole
      simp only [holeLength, List.length_map, List.length_range] at hfin
      obtain ⟨r, hr⟩ := hfin
      obtain ⟨k, hk⟩ := hodd
      have := PathBasics.pathLength_eq p
      omega
    · omega
  -- ======================================================================
  -- PAPER: *"Now suppose `P` has length `3`, and let its vertices be
  -- `p₁-⋯-p₄` in order."*
  -- ======================================================================
  · obtain hedge | ⟨h5, -⟩ | ⟨-, cc, dd, hint, q, hq, hqodd, hqint⟩ :=
      thm_2_1 G hG X hX p p₁ pn hp hpX hodd hp₁ hpn
    · exact absurd hedge hnoedge
    · omega
    -- PAPER: *"By 2.1, there is an odd antipath `Q` between `p₂` and `p₃` with
    -- interior in `X`."*
    · have hlen4 : p.length = 4 := by
        have := PathBasics.pathLength_eq p; omega
      obtain ⟨x0, x1, x2, x3, rfl⟩ := length_eq_four hlen4
      have hintv : SPGT.interior [x0, x1, x2, x3] = [x1, x2] := rfl
      rw [hintv] at hint
      obtain ⟨rfl, rfl⟩ : cc = x1 ∧ dd = x2 := by simpa using hint.symm
      -- `p₂p₃` is an edge of `P`
      have hadjcd : G.Adj cc dd :=
        (PathBasics.path_adj_iff hpl (i := 1) (j := 2)
          (by simp) (by simp)).mpr (Or.inl rfl)
      -- PAPER: *"it follows that `v` is adjacent to one of `p₂, p₃`"*; suppose not.
      by_contra hcon
      push Not at hcon
      have hmemcc : cc ∈ SPGT.interior [x0, cc, dd, x3] := by rw [hintv]; simp
      have hmemdd : dd ∈ SPGT.interior [x0, cc, dd, x3] := by rw [hintv]; simp
      have hnvc : ¬ G.Adj v cc := hcon cc hmemcc
      have hnvd : ¬ G.Adj v dd := hcon dd hmemdd
      have hvnc : v ≠ cc := by rintro rfl; exact hnvd hadjcd
      have hvnd : v ≠ dd := by rintro rfl; exact hnvc hadjcd.symm
      have hcv : Gᶜ.Adj v cc := (G.compl_adj v cc).mpr ⟨hvnc, hnvc⟩
      have hdv : Gᶜ.Adj v dd := (G.compl_adj v dd).mpr ⟨hvnd, hnvd⟩
      have hqp : IsPathFrom Gᶜ q cc dd := hq
      -- `Q` has length `≥ 3`: its ends `p₂, p₃` are adjacent in `G`.
      have hqlen1 : pathLength q ≠ 1 := fun h1 =>
        ((G.compl_adj cc dd).mp
          (PathBasics.isPathFrom_ends_adj_of_length_one hqp h1)).2 hadjcd
      have hqpos : 0 < q.length := PathBasics.path_length_pos hqp.1
      have hm4 : 4 ≤ q.length := by
        obtain ⟨k, hk⟩ := hqodd
        have := PathBasics.pathLength_eq q
        omega
      have hq0 : q[0]'(by omega) = cc := PathBasics.getElem_zero_of_head? hqp.2.1 (by omega)
      have hqlast : q[q.length - 1]'(by omega) = dd :=
        PathBasics.getElem_last_of_getLast? hqp.2.2 (by omega)
      have hqmemint : ∀ (k : ℕ) (hk : k < q.length), 1 ≤ k → k ≤ q.length - 2 →
          (q[k]'hk) ∈ SPGT.interior q := by
        intro k hk h1 h2
        rw [PathBasics.mem_interior_iff_of_pathFrom hqp]
        refine ⟨List.getElem_mem hk, ?_, ?_⟩
        · rw [← hq0]; exact PathBasics.path_ne_of_ne_index hqp.1 hk (by omega) (by omega)
        · rw [← hqlast]; exact PathBasics.path_ne_of_ne_index hqp.1 hk (by omega) (by omega)
      have hvnq : v ∉ q := fun hvq =>
        hvnX (hqint v ((PathBasics.mem_interior_iff_of_pathFrom hqp).mpr ⟨hvq, hvnc, hvnd⟩))
      -- PAPER: *"`Q` cannot be completed to an odd antihole via `p₃-v-p₂`."*
      -- The completion is the list `q ++ [v]`, encoded by the index function `g`.
      obtain ⟨g, hgm, hgq⟩ : ∃ g : ℕ → V, g q.length = v ∧
          ∀ (k : ℕ) (hk : k < q.length), g k = q[k]'hk := by
        refine ⟨fun k => if k = q.length then v else q.getD k v, by simp, ?_⟩
        intro k hk
        simp only [if_neg (show ¬ (k = q.length) by omega)]
        exact List.getD_eq_getElem q v hk
      have hgcases : ∀ k, k ≤ q.length →
          (k = q.length ∧ g k = v) ∨ (∃ hk : k < q.length, g k = q[k]'hk) := by
        intro k hk
        by_cases h : k = q.length
        · exact Or.inl ⟨h, by rw [h]; exact hgm⟩
        · exact Or.inr ⟨by omega, hgq k (by omega)⟩
      have hLq : ((List.range (q.length + 1)).map g).length = q.length + 1 := by simp
      have hgetq : ∀ (j : ℕ) (hj : j < ((List.range (q.length + 1)).map g).length),
          (((List.range (q.length + 1)).map g)[j]'hj) = g j := by
        intro j hj; simp
      have hhole : IsHoleList Gᶜ ((List.range (q.length + 1)).map g) := by
        refine isHoleList_of_le (by rw [hLq]; omega) ?_ ?_
        · refine List.Nodup.map_on ?_ List.nodup_range
          intro x hx y hy hxy
          rw [List.mem_range] at hx hy
          rcases hgcases x (by omega) with ⟨hx1, hex⟩ | ⟨hkx, hex⟩ <;>
            rcases hgcases y (by omega) with ⟨hy1, hey⟩ | ⟨hky, hey⟩
          · omega
          · exact absurd (show v ∈ q by
              rw [hex.symm.trans (hxy.trans hey)]; exact List.getElem_mem hky) hvnq
          · exact absurd (show v ∈ q by
              rw [hey.symm.trans (hxy.symm.trans hex)]; exact List.getElem_mem hkx) hvnq
          · by_contra hne
            exact PathBasics.path_ne_of_ne_index hqp.1 hkx hky hne
              (hex.symm.trans (hxy.trans hey))
        · intro i j hi hj hle
          have hi' : i ≤ q.length := by have h := hi; rw [hLq] at h; omega
          have hj' : j ≤ q.length := by have h := hj; rw [hLq] at h; omega
          rw [hgetq i hi, hgetq j hj, hLq, cyc_rhs (by omega) hi' hj' hle]
          rcases hgcases i hi' with ⟨hi1, hei⟩ | ⟨hki, hei⟩ <;>
            rcases hgcases j hj' with ⟨hj1, hej⟩ | ⟨hkj, hej⟩
          · rw [hei, hej]
            exact iff_of_false (SimpleGraph.irrefl _) (by omega)
          · exfalso; omega
          · rw [hei, hej]
            constructor
            · intro hadj
              by_contra hne
              have hmem := hqmemint i hki (by omega) (by omega)
              exact ((G.compl_adj _ _).mp hadj).2 (hvX _ (hqint _ hmem)).symm
            · intro _
              rcases (show i = 0 ∨ i = q.length - 1 by omega) with h | h
              · subst h; rw [hq0]; exact hcv.symm
              · subst h; rw [hqlast]; exact hdv.symm
          · rw [hei, hej, PathBasics.path_adj_iff hqp.1 hki hkj]
            omega
      -- `Q` together with `v` is an antihole of odd length: contradiction with `hG`.
      have hfin := hG.2 _ hhole
      simp only [holeLength, List.length_map, List.length_range] at hfin
      obtain ⟨r, hr⟩ := hfin
      obtain ⟨k, hk⟩ := hqodd
      have := PathBasics.pathLength_eq q
      omega


end SPGT

end Workspace.Statements.S02
