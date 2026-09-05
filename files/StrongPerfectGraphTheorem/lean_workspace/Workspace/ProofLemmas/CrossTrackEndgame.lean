import Mathlib
import Workspace.Types.Tracks
import Workspace.ProofLemmas.K33SubgraphBuilder

/-!
# The cross-track branch of Step 2 of 5.3: arithmetic core and endgame

The printed argument, once the second `K₄`-subdivision `H'` has been built and found degenerate:

> *"There is therefore a cycle of `H'` with vertex set `{r₁, r_t, p_m, q_n}`.  Since `H` is
> bipartite and `p_mq_n` is an edge, it follows that `t = 2`.  Hence not both `r₁ = p₁` and
> `r₂ = q₁`, and so `r₁ = p_{m−1}` and `r₂ = q_{n−1}`.  By the same argument with `p₁, p_m`
> exchanged, it follows that `r₁ = p₂`, and so `m = 3`, and similarly `n = 3`.  Hence there is a
> subgraph `J` of `H` isomorphic to `K₃,₃`."*

This module contains the three pieces of that paragraph that do **not** depend on the
construction of `H'`:

* `bipartite_no_triangle` — *"Since `H` is bipartite and `p_mq_n` is an edge"*.  This is what
  eliminates the third of the three candidate four-cycles: in that one `p_m` and `q_n` are
  **not** consecutive, so the edge `p_mq_n` is a chord, and together with the two cycle edges at
  `r_t` it makes a triangle.  (It can also be eliminated arithmetically — it forces `m = n = 2`,
  against `m, n ≥ 3` — but that is not the paper's argument, so it is not the one used.)
* `cross_track_indices` — the remaining arithmetic.  The six tracks of `H'` have lengths
  `t-1` (`R`), `m-1-i` (`r₁→p_m`), `i+1` (`r₁→q_n`), `j+1` (`r_t→p_m`), `n-1-j` (`r_t→q_n`) and
  `1` (`p_mq_n`), writing `r₁ = P[i]` and `r_t = Q[j]` with `0`-based indices.  Degeneracy makes
  four of them equal to `1`; the first candidate four-cycle would force `R` to be the excluded
  edge `p₁q₁`, so the second survives and gives `t = 2`, `i = m-2`, `j = n-2`.
* `m_eq_three_of_reversed` — *"By the same argument with `p₁, p_m` exchanged"*: re-running the
  argument on the reversed track puts `r₁` at index `m-1-i`, and the conclusion `i = m-2` applied
  to that index reads `m - 1 - i = m - 2`, whence `m = 3`.
* `exists_k33_of_len3` — the last sentence, feeding the resulting six vertices to
  `K33SubgraphBuilder.exists_k33_subgraph_of_six`.

The construction of `H'` itself is deliberately *not* here; see the report.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.CrossTrackEndgame

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.K33SubgraphBuilder

variable {W : Type*}

/-- A bipartite graph has no triangle.  (`K33SubgraphSpanning` has a `private` copy; this is the
public one, needed to eliminate the third candidate four-cycle.) -/
theorem bipartite_no_triangle {H : SimpleGraph W} (hbip : H.IsBipartite) {x y z : W}
    (h1 : H.Adj x y) (h2 : H.Adj x z) (h3 : H.Adj y z) : False := by
  obtain ⟨col⟩ := hbip
  have v1 := (col x).isLt
  have v2 := (col y).isLt
  have v3 := (col z).isLt
  have n1 : ((col x : ℕ)) ≠ ((col y : ℕ)) := fun h => col.valid h1 (Fin.val_injective h)
  have n2 : ((col x : ℕ)) ≠ ((col z : ℕ)) := fun h => col.valid h2 (Fin.val_injective h)
  have n3 : ((col y : ℕ)) ≠ ((col z : ℕ)) := fun h => col.valid h3 (Fin.val_injective h)
  omega

/-- **The arithmetic core.**

`hcase` lists the two candidate degenerate four-cycles that survive the triangle argument:
`r₁-r_t-p_m-q_n` (which forces `R` to be the edge `p₁q₁`, excluded by `hnotp1q1`) and
`r₁-r_t-q_n-p_m` (which is the truth). -/
theorem cross_track_indices {m n t i j : ℕ}
    (hm : 3 ≤ m) (hn : 3 ≤ n) (hi : i ≤ m - 2) (hj : j ≤ n - 2) (ht : 2 ≤ t)
    (hnotp1q1 : ¬ (t = 2 ∧ i = 0 ∧ j = 0))
    (hcase : (t - 1 = 1 ∧ j + 1 = 1 ∧ i + 1 = 1) ∨
      (t - 1 = 1 ∧ n - 1 - j = 1 ∧ m - 1 - i = 1)) :
    t = 2 ∧ i = m - 2 ∧ j = n - 2 := by
  omega

/-- **"By the same argument with `p₁, p_m` exchanged."**

Reversing `P` moves `r₁` from index `i` to index `m-1-i`; the conclusion `i = m-2` of
`cross_track_indices`, applied to the reversed configuration, therefore reads
`m - 1 - i = m - 2`. -/
theorem m_eq_three_of_reversed {m i : ℕ} (hm : 3 ≤ m) (h1 : i = m - 2)
    (h2 : m - 1 - i = m - 2) : m = 3 := by
  omega

/-- **The last sentence.**  With `m = n = 3` and `R = p₂-q₂`, the six vertices span a `K₃,₃`. -/
theorem exists_k33_of_len3 {H : SimpleGraph W} {P Q : List W}
    (hP : IsTrackList H P) (hQ : IsTrackList H Q)
    (hPlen : P.length = 3) (hQlen : Q.length = 3)
    (hdisj : ∀ x ∈ P, x ∉ Q)
    (e11 : H.Adj P[0] Q[0]) (e1n : H.Adj P[0] Q[2])
    (em1 : H.Adj P[2] Q[0]) (emn : H.Adj P[2] Q[2])
    (eR : H.Adj P[1] Q[1]) :
    ∃ J : H.Subgraph, Nonempty (J.coe ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := by
  have h01 : H.Adj P[0] P[1] := hP.2.2 0 (by omega)
  have h12 : H.Adj P[1] P[2] := hP.2.2 1 (by omega)
  have g01 : H.Adj Q[0] Q[1] := hQ.2.2 0 (by omega)
  have g12 : H.Adj Q[1] Q[2] := hQ.2.2 1 (by omega)
  -- the six vertices are pairwise distinct
  have hPd : ∀ (a b : ℕ) (ha : a < P.length) (hb : b < P.length),
      a ≠ b → (P[a]'ha) ≠ (P[b]'hb) := by
    intro a b ha hb hab hc
    exact hab (hP.2.1.getElem_inj_iff.mp hc)
  have hQd : ∀ (a b : ℕ) (ha : a < Q.length) (hb : b < Q.length),
      a ≠ b → (Q[a]'ha) ≠ (Q[b]'hb) := by
    intro a b ha hb hab hc
    exact hab (hQ.2.1.getElem_inj_iff.mp hc)
  have hX : ∀ (a b : ℕ) (ha : a < P.length) (hb : b < Q.length), (P[a]'ha) ≠ (Q[b]'hb) := by
    intro a b ha hb hc
    exact hdisj _ (List.getElem_mem ha) (by rw [hc]; exact List.getElem_mem hb)
  have d01 := hPd 0 1 (by omega) (by omega) (by omega)
  have d02 := hPd 0 2 (by omega) (by omega) (by omega)
  have d12 := hPd 1 2 (by omega) (by omega) (by omega)
  have e01 := hQd 0 1 (by omega) (by omega) (by omega)
  have e02 := hQd 0 2 (by omega) (by omega) (by omega)
  have e12 := hQd 1 2 (by omega) (by omega) (by omega)
  have x00 := hX 0 0 (by omega) (by omega)
  have x01 := hX 0 1 (by omega) (by omega)
  have x02 := hX 0 2 (by omega) (by omega)
  have x10 := hX 1 0 (by omega) (by omega)
  have x11 := hX 1 1 (by omega) (by omega)
  have x12 := hX 1 2 (by omega) (by omega)
  have x20 := hX 2 0 (by omega) (by omega)
  have x21 := hX 2 1 (by omega) (by omega)
  have x22 := hX 2 2 (by omega) (by omega)
  have hnd : [P[0], P[1], P[2], Q[0], Q[1], Q[2]].Nodup := by
    simp [d01, d02, d12, e01, e02, e12, x00, x01, x02, x10, x11, x12, x20, x21, x22]
  exact exists_k33_subgraph_of_six P[0] P[1] P[2] Q[0] Q[1] Q[2] hnd
    e11 e1n h01 em1 emn h12.symm g01.symm g12 eR.symm

end Workspace.ProofLemmas.CrossTrackEndgame
