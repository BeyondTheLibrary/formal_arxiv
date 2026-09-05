/-  Proof of the 9.6 leaf `DegenerateK4AppearanceYieldsStriation`.

PAPER (9.6, printed p. 55): *"Now we may assume that there is an appearance of `K₄` in `G` say.
By hypothesis it is degenerate, and hence there is a striation in `G`."*

The two halves of that *"hence"* are the two §9-preamble facts already established:

* *"If `L(H)` is a degenerate appearance of `K₄` in `G`, it can be viewed as a knot"* — printed
  p. 47 — is `KnotFromDegenerateAppearance.exists_knot_of_degenerate_appearance`;
* the knot so obtained has both antipaths of length `1` and both paths of odd length, which by
  `StriationFromKnot.exists_striation_of_knot` is a striation (`m = n = 2`). -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Knots
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.KnotFromDegenerateAppearance
import Workspace.ProofLemmas.StriationFromKnot

set_option autoImplicit false

namespace Workspace.ProofLemmas.DegenerateK4AppearanceYieldsStriation

open Workspace.Types.Appearances.SPGT
open Workspace.Types.Knots.SPGT

/-- A degenerate `K₄` appearance yields a striation. -/
theorem degenerateK4AppearanceYieldsStriation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hdegenerate : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K →
        DegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H)
    (happears : Appears G (⊤ : SimpleGraph (Fin 4))) :
    ∃ (m n : ℕ) (S : Fin m → Set V × Set V × Set V)
      (T : Fin n → Set V × Set V × Set V),
      IsStriation G S T := by
  -- PAPER: *"there is an appearance of `K₄` in `G`"*.
  obtain ⟨n, H, K, happ⟩ := happears
  -- PAPER: *"By hypothesis it is degenerate"*.
  have hdeg : DegenerateK4Appearance H :=
    ClassLemmas.degenerateAppearance_K4_iff.mp (hdegenerate n H K happ)
  -- PAPER (§9 preamble, p. 47): *"If `L(H)` is a degenerate appearance of `K₄` in `G`, it can
  -- be viewed as a knot."*
  obtain ⟨P₁, P₂, Q₁, Q₂, hknot, hQ₁, hQ₂, hoP₁, hoP₂⟩ :=
    KnotFromDegenerateAppearance.exists_knot_of_degenerate_appearance G happ hdeg
  -- PAPER: *"and hence there is a striation in `G`"*.
  exact StriationFromKnot.exists_striation_of_knot G hknot hQ₁ hQ₂ hoP₁ hoP₂

end Workspace.ProofLemmas.DegenerateK4AppearanceYieldsStriation
