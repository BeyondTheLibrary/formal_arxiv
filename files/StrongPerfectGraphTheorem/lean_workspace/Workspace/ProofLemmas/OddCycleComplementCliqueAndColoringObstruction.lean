import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic
import Workspace.ProofLemmas.OddCycleCliqueAndTwoColoringObstruction

set_option autoImplicit false

namespace Workspace.ProofLemmas

/-- The complement of an odd cycle on `2 * m + 1` vertices, for `m ≥ 2`, has
clique number `m` and is not `m`-colorable. -/
theorem OddCycleComplementCliqueAndColoringObstruction
    (m : ℕ) (hm : 2 ≤ m) :
    let A := (SimpleGraph.cycleGraph (2 * m + 1))ᶜ
    A.cliqueNum = m ∧ ¬ A.Colorable m := by
  dsimp
  let e : Fin m ↪ Fin (2 * m + 1) := {
    toFun r := ⟨2 * r.val, by omega⟩
    inj' := by
      intro r s hrs
      apply Fin.ext
      have hval := congrArg Fin.val hrs
      dsimp at hval
      omega }
  let t : Finset (Fin (2 * m + 1)) := Finset.univ.map e
  have htind : (SimpleGraph.cycleGraph (2 * m + 1)).IsIndepSet t := by
    intro x hx y hy hxy hadj
    simp only [t, Finset.mem_coe, Finset.mem_map, Finset.mem_univ, true_and] at hx hy
    obtain ⟨r, rfl⟩ := hx
    obtain ⟨s, rfl⟩ := hy
    rw [SimpleGraph.cycleGraph_adj'] at hadj
    rcases hadj with hsub | hsub
    · have hsubZ : (((e r - e s).val : ℤ) = 1) := by omega
      rw [Fin.intCast_val_sub_eq_sub_add_ite] at hsubZ
      dsimp [e] at hsubZ
      split_ifs at hsubZ <;> omega
    · have hsubZ : (((e s - e r).val : ℤ) = 1) := by omega
      rw [Fin.intCast_val_sub_eq_sub_add_ite] at hsubZ
      dsimp [e] at hsubZ
      split_ifs at hsubZ <;> omega
  have htclique : ((SimpleGraph.cycleGraph (2 * m + 1))ᶜ).IsClique t :=
    (SimpleGraph.isClique_compl (G := SimpleGraph.cycleGraph (2 * m + 1))).mpr htind
  constructor
  · apply le_antisymm
    · obtain ⟨s, hs⟩ :=
        ((SimpleGraph.cycleGraph (2 * m + 1))ᶜ).exists_isNClique_cliqueNum
      rw [← hs.card_eq]
      have hsind : (SimpleGraph.cycleGraph (2 * m + 1)).IsIndepSet s :=
        (SimpleGraph.isClique_compl (G := SimpleGraph.cycleGraph (2 * m + 1))).mp hs.isClique
      let succ : Fin (2 * m + 1) ↪ Fin (2 * m + 1) := {
        toFun x := x + 1
        inj' := by
          intro x y hxy
          exact add_right_cancel hxy }
      have hdisj : Disjoint s (s.map succ) := by
        rw [Finset.disjoint_left]
        intro x hx hxim
        rw [Finset.mem_map] at hxim
        obtain ⟨y, hy, rfl⟩ := hxim
        have hadj : (SimpleGraph.cycleGraph (2 * m + 1)).Adj y (y + 1) := by
          rw [SimpleGraph.cycleGraph_adj']
          right
          have heq : y + 1 - y = (1 : Fin (2 * m + 1)) := by abel
          rw [heq]
          simpa only [Fin.val_one'] using
            (Nat.mod_eq_of_lt (by omega : 1 < 2 * m + 1))
        exact hsind hy hx hadj.ne hadj
      have hcard : (s ∪ s.map succ).card ≤ 2 * m + 1 := by
        simpa using Finset.card_le_univ (s ∪ s.map succ)
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_map] at hcard
      omega
    · have hcard : t.card = m := by simp [t]
      calc
        m = t.card := hcard.symm
        _ ≤ ((SimpleGraph.cycleGraph (2 * m + 1))ᶜ).cliqueNum :=
          htclique.card_le_cliqueNum
  · intro hcolor
    obtain ⟨C⟩ := hcolor
    have hpigeon : Fintype.card (Fin m) * 2 < Fintype.card (Fin (2 * m + 1)) := by
      simp only [Fintype.card_fin]
      omega
    obtain ⟨a, ha⟩ :=
      Fintype.exists_lt_card_fiber_of_mul_lt_card (f := fun x ↦ C x) hpigeon
    let s : Finset (Fin (2 * m + 1)) := Finset.univ.filter fun x ↦ C x = a
    have hsClique : (SimpleGraph.cycleGraph (2 * m + 1)).IsClique s := by
      rw [← SimpleGraph.isIndepSet_compl]
      simpa [s, SimpleGraph.Coloring.colorClass] using C.isIndepSet_colorClass a
    have hsle := hsClique.card_le_cliqueNum
    have hcycle := OddCycleCliqueAndTwoColoringObstruction
      (2 * m + 1) (by omega) (by exact ⟨m, rfl⟩)
    rw [hcycle.1] at hsle
    change 2 < s.card at ha
    omega

end Workspace.ProofLemmas
