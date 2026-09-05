import Workspace.Types.Core
import Workspace.ProofLemmas.CliqueNumOfInducedSet
import Workspace.ProofLemmas.IndependentSetColoringExtension

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT

/-- A nonempty stable set meeting every maximum clique extends a perfect
remainder coloring to a clique-number coloring of the whole graph. -/
theorem StableTransversalWithPerfectRemainderColorable
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) (S : Set V)
    (hSne : S.Nonempty)
    (hSstable : K.IsIndepSet S)
    (hperfect : IsPerfect (K.induce Sᶜ))
    (hhits : ∀ Q : Finset V, K.IsClique (↑Q : Set V) → Q.card = K.cliqueNum →
      ∃ q : V, q ∈ Q ∧ q ∈ S) :
    K.Colorable K.cliqueNum := by
  classical
  obtain ⟨Q, hQR, hQclique, hQcard⟩ :=
    CliqueNumOfInducedSet.exists_clique_card_eq_cliqueNum K Sᶜ
  have hclique_le : (K.induce Sᶜ).cliqueNum ≤ K.cliqueNum := by
    rw [← hQcard]
    exact SimpleGraph.IsClique.card_le_cliqueNum (tc := hQclique)
  have hclique_ne : (K.induce Sᶜ).cliqueNum ≠ K.cliqueNum := by
    intro heq
    obtain ⟨q, hqQ, hqS⟩ := hhits Q hQclique (hQcard.trans heq)
    exact (hQR hqQ) hqS
  have hclique_lt : (K.induce Sᶜ).cliqueNum < K.cliqueNum :=
    lt_of_le_of_ne hclique_le hclique_ne
  obtain ⟨cR⟩ :=
    CliqueNumOfInducedSet.colorable_cliqueNum_of_isPerfect (K.induce Sᶜ) hperfect
  let Y : Set V := Set.univ
  let S' : Set Y := {y | (y : V) ∈ S}
  have hS' : (K.induce Y).IsIndepSet S' := by
    intro a ha b hb hab
    exact hSstable ha hb (fun h => hab (Subtype.ext h))
  let lift (y : Y) (hy : y ∉ S') : (Sᶜ : Set V) :=
    ⟨y.1, by simpa [S'] using hy⟩
  have hcY : (K.induce Y).Colorable ((K.induce Sᶜ).cliqueNum + 1) :=
    IndependentSetColoringExtension K Y Sᶜ S' hS' cR lift (by
      intro a b ha hb hab
      exact hab)
  have hcK : K.Colorable ((K.induce Sᶜ).cliqueNum + 1) :=
    SimpleGraph.Colorable.of_hom (SimpleGraph.induceUnivIso K).symm.toHom hcY
  exact hcK.mono (Nat.succ_le_iff.mpr hclique_lt)

end Workspace.ProofLemmas
