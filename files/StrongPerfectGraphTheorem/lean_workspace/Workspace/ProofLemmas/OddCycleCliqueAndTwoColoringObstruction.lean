import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

set_option autoImplicit false

namespace Workspace.ProofLemmas

/-- An odd cycle of length at least five has clique number two and is not
two-colorable. -/
theorem OddCycleCliqueAndTwoColoringObstruction
    (n : ℕ) (hn : 5 ≤ n) (hodd : Odd n) :
    (SimpleGraph.cycleGraph n).cliqueNum = 2 ∧
      ¬ (SimpleGraph.cycleGraph n).Colorable 2 := by
  constructor
  · have htriangleFree : (SimpleGraph.cycleGraph n).CliqueFree 3 := by
      intro t ht
      rw [SimpleGraph.is3Clique_iff] at ht
      obtain ⟨a, b, c, hab, hac, hbc, -⟩ := ht
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
      simp only [SimpleGraph.cycleGraph_adj] at hab hac hbc
      have hsub {x y : Fin (k + 5)} (h : x - y = 1) :
          (x.val : ℤ) - y.val + (if y ≤ x then 0 else k + 5) = 1 := by
        have hval := congrArg (fun z : Fin (k + 5) => (z.val : ℤ)) h
        simpa only [Fin.intCast_val_sub_eq_sub_add_ite, Fin.val_one', Nat.cast_one] using hval
      have habZ := hab.imp hsub hsub
      have hacZ := hac.imp hsub hsub
      have hbcZ := hbc.imp hsub hsub
      rcases habZ with habZ | habZ <;>
        rcases hacZ with hacZ | hacZ <;>
        rcases hbcZ with hbcZ | hbcZ <;>
        split_ifs at habZ hacZ hbcZ <;> omega
    let v0 : Fin n := ⟨0, by omega⟩
    let v1 : Fin n := ⟨1, by omega⟩
    have hadj : (SimpleGraph.cycleGraph n).Adj v0 v1 := by
      simp [v0, v1, SimpleGraph.cycleGraph_adj', Fin.sub_val_of_le]
    have hmax : (SimpleGraph.cycleGraph n).IsMaximumClique {v0, v1} := by
      constructor
      · simpa using (SimpleGraph.isClique_pair.mpr fun _ ↦ hadj)
      · intro t ht
        have hpaircard : ({v0, v1} : Finset (Fin n)).card = 2 := by
          simp [v0, v1]
        by_contra hcard
        have hthree : 3 ≤ t.card := by omega
        obtain ⟨u, hu, hucard⟩ := Finset.exists_subset_card_eq hthree
        exact htriangleFree u ⟨ht.subset hu, hucard⟩
    have hcard :=
      SimpleGraph.maximumClique_card_eq_cliqueNum ({v0, v1} : Finset (Fin n)) hmax
    simpa [v0, v1] using hcard.symm
  · intro hcolor
    have hle := hcolor.chromaticNumber_le
    rw [SimpleGraph.chromaticNumber_cycleGraph_of_odd n (by omega) hodd] at hle
    exact (by decide : ¬ (3 : ℕ∞) ≤ 2) hle

end Workspace.ProofLemmas
