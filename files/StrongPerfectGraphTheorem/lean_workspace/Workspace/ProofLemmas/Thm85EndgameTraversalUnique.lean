import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.Thm85EndgameNotions
import Workspace.ProofLemmas.Thm85EndgameK4Shape

/-!
# 8.5, claim (4): the traversal is unique

The existence half of claim (4) is proved in `Thm85EndgameClaim4`.  This module isolates the
uniqueness half, which is the only part of claim (4) that goes through the degeneracy analysis
of §8: it exhibits `J` as `K₄` with four rungs of length `0` and contradicts the second bullet
of claim (1).

**Repaired statement.**  As written by the earlier agent the theorem was false: `IsTraversal`
is symmetric under exchanging `(i,j)` with `(j,i)` and `f₁` with `f_n` at the same time, so if
`f₁ = f_n` then `(j,i)` is a traversal whenever `(i,j)` is, and the conclusion `i' = i ∧ j' = j`
fails.  (A concrete configuration: `J = K₃,₃` with parts `{i,a,b}`, `{j,c,d}`, all strips single
vertices, and `F = {f}` a single vertex adjacent to the four strips `S_ic, S_id, S_ja, S_jb`.)
The hypothesis `f₁ ≠ f_n` — the paper's `n ≥ 2` — has therefore been added; see
`lean_workspace/REPORT.md`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm85EndgameTraversalUnique

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.ProofLemmas.Thm85EndgameNotions

/-- **Gap: the uniqueness half of claim (4) of 8.5** (printed pp. 43–44).

PAPER: *"Hence there is an edge `ij` as in (4).  Suppose there is another, say `i'j'`.  Since
`i'j'` meets all edges of `J` that share exactly one end with `ij`, and `J` is 3-connected, it
follows that `J = K₄` and the two edges `ij`, `i'j'` are disjoint.  Moreover, the unique vertex
of `R_{ii'}` in `X` is both `r_{ii'}` and `r_{i'i}`, so `R_{ii'}` has length 0.  Similarly
`R_{ij'}`, `R_{ji'}`, `R_{jj'}` all have length 0, and so `L(H)` is degenerate, contrary to (1).
This proves (4)."*

The hypotheses are those of claim (4): `hclaim1` is claim (1), whose second bullet supplies the
nondegeneracy of `L(H)` when `J = K₄`, and `f₁ ≠ f_n` is not needed — the two traversals are for
the *same* choice of rungs `R`. -/
theorem traversal_unique {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (F : Set V) (f₁ fn : V)
    (hclaim1 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (R : U → U → List V) (K : Set V)
        (phi : H.lineGraph ≃g G.induce K),
        K = ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v} →
        FormsLineGraph G J S N R H →
        (∀ y ∈ F, ¬ SaturatesLineGraph H
            {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
              (↑(phi ⟨e, he⟩) : V) ∈ G.neighborSet y}) ∧
        (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateAppearance J H))
    (hfne : f₁ ≠ fn)
    (R : U → U → List V) (hR : RungChoice G J S N R)
    (i j i' j' : U)
    (htrav : IsTraversal G J N F f₁ fn R i j)
    (htrav' : IsTraversal G J N F f₁ fn R i' j') :
    i' = i ∧ j' = j := by
  classical
  have hij : J.Adj i j := htrav.1
  have hij' : J.Adj i' j' := htrav'.1
  by_cases h1 : i' = i
  · by_cases h2 : j' = j
    · exact ⟨h1, h2⟩
    · -- `i' = i` and `j' ≠ j`: an edge at `j` avoiding `i` and `j'` is attached to `F`,
      -- yet it is disjoint from `i'j'`.
      exfalso
      rw [h1] at htrav' hij'
      obtain ⟨w, hjw, hwi, hwj'⟩ := Thm85EndgameK4Shape.exists_adj_ne_two hJ j i j'
      obtain ⟨r, -, -, hu⟩ := htrav.2.2.1 w hwi hjw
      have hjwne : j ≠ w := hjw.ne
      have h3 : j ≠ i := hij.ne'
      have h4 : j ≠ j' := fun h => h2 h.symm
      have h5 : i ≠ j' := hij'.ne
      have hnd : [j, w, i, j'].Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
          and_true, not_or]
        tauto
      exact htrav'.2.2.2 j w hjw hnd r hu.1 fn hu.2.1 hu.2.2.1
  · by_cases h2 : i' = j
    · rw [h2] at htrav' hij'
      by_cases h3 : j' = i
      · -- the reversed pair: the two uniqueness clauses at one edge force `f₁ = f_n`
        exfalso
        rw [h3] at htrav' hij'
        obtain ⟨w, hiw, hwj, -⟩ := Thm85EndgameK4Shape.exists_adj_ne_two hJ i j j
        obtain ⟨r, -, -, hu⟩ := htrav.2.1 w hwj hiw
        obtain ⟨r', -, -, hu'⟩ := htrav'.2.2.1 w hwj hiw
        exact hfne (hu.2.2.2 r' hu'.1 fn hu'.2.1 hu'.2.2.1).2.symm
      · -- `i' = j` and `j' ≠ i`: an edge at `i` avoiding `j` and `j'` is attached to `F`
        exfalso
        obtain ⟨w, hiw, hwj, hwj'⟩ := Thm85EndgameK4Shape.exists_adj_ne_two hJ i j j'
        obtain ⟨r, -, -, hu⟩ := htrav.2.1 w hwj hiw
        have hiwne : i ≠ w := hiw.ne
        have h4 : i ≠ j := hij.ne
        have h5 : i ≠ j' := fun h => h3 h.symm
        have h6 : j ≠ j' := hij'.ne
        have hnd : [i, w, j, j'].Nodup := by
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
            and_true, not_or]
          tauto
        exact htrav'.2.2.2 i w hiw hnd r hu.1 f₁ hu.2.1 hu.2.2.1
    · by_cases h3 : j' = j
      · -- `j' = j`, `i' ∉ {i,j}`: an edge at `i` avoiding `j` and `i'` is attached to `F`
        exfalso
        rw [h3] at htrav' hij'
        obtain ⟨w, hiw, hwj, hwi'⟩ := Thm85EndgameK4Shape.exists_adj_ne_two hJ i j i'
        obtain ⟨r, -, -, hu⟩ := htrav.2.1 w hwj hiw
        have hiwne : i ≠ w := hiw.ne
        have h4 : i ≠ i' := fun h => h1 h.symm
        have h5 : i ≠ j := hij.ne
        have h6 : i' ≠ j := hij'.ne
        have hnd : [i, w, i', j].Nodup := by
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
            and_true, not_or]
          tauto
        exact htrav'.2.2.2 i w hiw hnd r hu.1 f₁ hu.2.1 hu.2.2.1
      · by_cases h4 : j' = i
        · -- `j' = i`, `i' ∉ {i,j}`: an edge at `j` avoiding `i` and `i'` is attached to `F`
          exfalso
          rw [h4] at htrav' hij'
          obtain ⟨w, hjw, hwi, hwi'⟩ := Thm85EndgameK4Shape.exists_adj_ne_two hJ j i i'
          obtain ⟨r, -, -, hu⟩ := htrav.2.2.1 w hwi hjw
          have hjwne : j ≠ w := hjw.ne
          have h5 : j ≠ i' := fun h => h2 h.symm
          have h6 : j ≠ i := hij.ne'
          have h7 : i' ≠ i := hij'.ne
          have hnd : [j, w, i', i].Nodup := by
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
              and_true, not_or]
            tauto
          exact htrav'.2.2.2 j w hjw hnd r hu.1 fn hu.2.1 hu.2.2.1
        · -- the two edges are disjoint: this is the printed `K₄` argument
          exfalso
          have h5 : i ≠ j := hij.ne
          have h6 : i ≠ i' := fun h => h1 h.symm
          have h7 : i ≠ j' := fun h => h4 h.symm
          have h8 : j ≠ i' := fun h => h2 h.symm
          have h9 : j ≠ j' := fun h => h3 h.symm
          have h10 : i' ≠ j' := hij'.ne
          have hnd : [i, j, i', j'].Nodup := by
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
              and_true, not_or]
            tauto
          exact Thm85EndgameK4Shape.disjoint_traversals_absurd G hG J hJ S N hSN F f₁ fn
            hclaim1 R hR i j i' j' hnd hij htrav.2.1 htrav.2.2.1 htrav'

end Workspace.ProofLemmas.Thm85EndgameTraversalUnique
