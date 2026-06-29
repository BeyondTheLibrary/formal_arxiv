import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.GaussianMixture2
import Workspace.Types.SignedGaussianCombination

namespace Workspace.ProofLemmas

theorem MixtureDifferenceAsSignedCombination
    (G G' : Workspace.Types.GaussianMixture2.GaussianMixture2) :
    ∃ S : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination,
      S.components.length = 4 ∧
      (∀ x : ℝ, S.density x = G.density x - G'.density x) ∧
      S.components = [(G.weight1, G.comp1), (G.weight2, G.comp2),
                       (-G'.weight1, G'.comp1), (-G'.weight2, G'.comp2)] := by
  refine ⟨⟨[(G.weight1, G.comp1), (G.weight2, G.comp2),
            (-G'.weight1, G'.comp1), (-G'.weight2, G'.comp2)]⟩, ?_, ?_, ?_⟩
  · rfl
  · intro x
    simp [Workspace.Types.SignedGaussianCombination.SignedGaussianCombination.density,
          Workspace.Types.GaussianMixture2.GaussianMixture2.density]
    ring
  · rfl

end Workspace.ProofLemmas
