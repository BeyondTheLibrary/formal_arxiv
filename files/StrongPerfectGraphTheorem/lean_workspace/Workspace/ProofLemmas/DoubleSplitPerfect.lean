import Workspace.Types.BasicClasses
import Workspace.Types.Core
import Workspace.ProofLemmas.ColoringCliqueSandwich
import Workspace.ProofLemmas.DoubleSplitNoActiveColorClique
import Workspace.ProofLemmas.DoubleSplitUniversalColorClique
import Workspace.ProofLemmas.DoubleSplitSafeColorClique

set_option autoImplicit false

namespace Workspace.ProofLemmas

/-- Every finite double split graph is perfect. -/
theorem DoubleSplitPerfect
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W)
    (hK : Workspace.Types.BasicClasses.SPGT.IsDoubleSplitGraph K) :
    Workspace.Types.Core.SPGT.IsPerfect K := by
  classical
  rcases hK with ⟨m, n, a, b, c, d, hm, hn, hbij, hab, hcd, hleft, hright, hcross⟩
  intro X
  letI : DecidablePred (fun j : Fin n => c j ∈ X ∨ d j ∈ X) := Classical.decPred _
  let J : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => c j ∈ X ∨ d j ∈ X)
  have hmem_J : ∀ j : Fin n, j ∈ J ↔ c j ∈ X ∨ d j ∈ X := by
    intro j
    simp [J]
  by_cases hJ : J = ∅
  · obtain ⟨k, hcolor, hclique⟩ :=
      DoubleSplitNoActiveColorClique K m n a b c d hm hn hbij hab hcd hleft hright hcross X (by
        apply Finset.not_nonempty_iff_eq_empty.mp
        rintro ⟨j, hj⟩
        have hjJ : j ∈ J := (hmem_J j).2 (by
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj)
        rw [hJ] at hjJ
        simp at hjJ)
    exact ColoringCliqueSandwich (K.induce X) k hcolor hclique
  · have hJne : J.Nonempty := Finset.nonempty_iff_ne_empty.mpr hJ
    by_cases hUniversal : ∃ z : W,
        z ∈ X ∧ (∃ i : Fin m, z = a i ∨ z = b i) ∧
          ∀ j : Fin n, j ∈ J →
            ∃ y : W, y ∈ X ∧ (y = c j ∨ y = d j) ∧ K.Adj z y
    · obtain ⟨hcolor, hclique⟩ :=
        DoubleSplitUniversalColorClique K m n a b c d hm hn hbij hab hcd hleft hright hcross X
          (by
            rcases hJne with ⟨j, hj⟩
            refine ⟨j, ?_⟩
            simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using (hmem_J j).1 hj)
          (by
            rcases hUniversal with ⟨z, hzX, hzleft, hzall⟩
            refine ⟨z, hzX, hzleft, ?_⟩
            intro j hj
            apply hzall j
            exact (hmem_J j).2 (by
              simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj))
      exact ColoringCliqueSandwich (K.induce X) _ hcolor hclique
    · obtain ⟨hcolor, hclique⟩ :=
        DoubleSplitSafeColorClique K m n a b c d hm hn hbij hab hcd hleft hright hcross X
          (by
            rcases hJne with ⟨j, hj⟩
            refine ⟨j, ?_⟩
            simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using (hmem_J j).1 hj)
          (by
            intro hsafe
            apply hUniversal
            rcases hsafe with ⟨z, hzX, hzleft, hzall⟩
            refine ⟨z, hzX, hzleft, ?_⟩
            intro j hj
            apply hzall j
            simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using (hmem_J j).1 hj)
      exact ColoringCliqueSandwich (K.induce X) _ hcolor hclique

end Workspace.ProofLemmas
