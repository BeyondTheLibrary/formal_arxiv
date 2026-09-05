import Workspace.Types.Core
import Workspace.ProofLemmas.CriticalImperfectComplement
import Workspace.ProofLemmas.AntitwinExtremalClique

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core

/-- A critical-imperfect antitwin pair has a nonempty stable set on its `u`-side
that is maximal against vertices on either antitwin side. -/
theorem AntitwinDualExtremalStableSet
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W)
    (hKnonperfect : ¬ SPGT.IsPerfect K)
    (hKproper : ∀ X : Set W, X ≠ Set.univ → SPGT.IsPerfect (K.induce X))
    (u v : W) (huv : u ≠ v)
    (hanti : ∀ z : W, z ≠ u → z ≠ v →
      Xor' (K.Adj z u) (K.Adj z v)) :
    ∃ R : Set W,
      R ⊆ {z : W | z ≠ u ∧ z ≠ v ∧ K.Adj z u} ∧
      R.Nonempty ∧
      Set.Pairwise R (fun x y => ¬ K.Adj x y) ∧
      ∀ z : W,
        z ∈ (({x : W | x ≠ u ∧ x ≠ v ∧ K.Adj x u} ∪
          {x : W | x ≠ u ∧ x ≠ v ∧ K.Adj x v}) \ R) →
        ∃ r ∈ R, K.Adj z r := by
  classical
  obtain ⟨hKcnonperfect, hKcproper⟩ :=
    CriticalImperfectComplement K hKnonperfect hKproper
  have hantic : ∀ z : W, z ≠ u → z ≠ v →
      Xor' ((Kᶜ).Adj z u) ((Kᶜ).Adj z v) := by
    intro z hzu hzv
    rw [SimpleGraph.compl_adj, SimpleGraph.compl_adj]
    simpa [hzu, hzv] using xor_not_not.mpr (hanti z hzu hzv)
  obtain ⟨R, hRsub, hRnonempty, hRclique, hRmax⟩ :=
    AntitwinExtremalClique Kᶜ hKcnonperfect hKcproper u v huv hantic
  refine ⟨R, ?_, hRnonempty, ?_, ?_⟩
  · intro z hz
    rcases hRsub hz with ⟨hzu, hzv, hzcv⟩
    rw [SimpleGraph.compl_adj] at hzcv
    refine ⟨hzu, hzv, ?_⟩
    rcases hanti z hzu hzv with hzu' | hzv'
    · exact hzu'.1
    · exact (hzcv.2 hzv'.1).elim
  · simpa only [SimpleGraph.isClique_compl, SimpleGraph.isIndepSet_iff] using hRclique
  · intro z hz
    rcases hz with ⟨hzside, hznotR⟩
    have hzcside :
        z ∈ (({x : W | x ≠ u ∧ x ≠ v ∧ (Kᶜ).Adj x u} ∪
          {x : W | x ≠ u ∧ x ≠ v ∧ (Kᶜ).Adj x v}) \ R) := by
      refine ⟨?_, hznotR⟩
      rcases hzside with hzP | hzQ
      · rcases hzP with ⟨hzu, hzv, hzku⟩
        refine Or.inr ⟨hzu, hzv, ?_⟩
        rw [SimpleGraph.compl_adj]
        refine ⟨hzv, ?_⟩
        rcases hanti z hzu hzv with hzu' | hzv'
        · exact hzu'.2
        · exact (hzv'.2 hzku).elim
      · rcases hzQ with ⟨hzu, hzv, hzkv⟩
        refine Or.inl ⟨hzu, hzv, ?_⟩
        rw [SimpleGraph.compl_adj]
        refine ⟨hzu, ?_⟩
        rcases hanti z hzu hzv with hzu' | hzv'
        · exact (hzu'.2 hzkv).elim
        · exact hzv'.2
    obtain ⟨r, hrR, hzrc⟩ := hRmax z hzcside
    refine ⟨r, hrR, ?_⟩
    have hzr : z ≠ r := by
      intro hzr
      apply hznotR
      simpa only [hzr] using hrR
    by_contra hzrK
    apply hzrc
    rw [SimpleGraph.compl_adj]
    exact ⟨hzr, hzrK⟩

end Workspace.ProofLemmas

