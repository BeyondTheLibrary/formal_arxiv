import Mathlib
import Workspace.ProofLemmas.Thm106Assembly
import Workspace.ProofLemmas.HyperprismEndgame
import Workspace.ProofLemmas.HyperprismSkewFromSide

/-!
# 10.6: the two steps of `Thm106Assembly` that are proved

`Thm106Assembly.thm_10_6_of_steps` reduces **10.6** to three `def`-wrapped steps, `Claim2`,
`SkewFromSide` and `Endgame`.  Two of the three are proved; this module discharges them, so
that closing the node needs only `Claim2`:

```
thm_10_6_of_steps G hG hK4 <Claim2 proof> skewFromSide endgame heven
```

* `skewFromSide` is `HyperprismSkewFromSide.admitsBalancedSkewPartition_of_attachments_subset_A`
  (P7 — claim (3) of the printed proof, printed p. 62).  `SkewFromSide` additionally
  quantifies over `MaximalHyperprism G A B C`, which claim (3) does not consume: the printed
  argument uses only that the nine sets *are* a hyperprism.  The extra hypothesis is discarded.

* `endgame` is `HyperprismEndgame.thm_10_6_endgame` (P8 — the closing paragraph, printed
  p. 63), plus one patch.  P8 asks for
  `hne : every nonempty component of V(G) \ V(H) has a nonempty attachment set`, which
  `Endgame` does not carry, and which the paper has in force as a standing assumption from the
  sentence *"So we may assume there is no such `F`, and the same for `B`"* two sentences
  earlier.  A component with **no** attachments has, vacuously, all of them in `A`, so claim
  (3) applies to it and gives `AdmitsBalancedSkewPartition G` — the third disjunct of
  `Thm106Conclusion` — outright.  That is the `by_cases` below.

  Why `hne` is not optional: the paper's `X` is *"the union of `S₁` and all components of
  `V(G) \ V(H)` whose attachment set is a subset of `S₁`"*, and an attachment-free component
  qualifies for `S₁`, `S₂` and `S₃` at once, so `(X, Y)` would not be a partition.

`ProofAttempts/thm_10_6/SkewFromSideCheck.lean` and `ProofAttempts/thm_10_6/EndgameCheck.lean`
are the interface checks for the two steps; they also spell the two `def` bodies out verbatim,
so that a drift in either `def` is caught.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm106Steps

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Step (3) of the printed proof of 10.6** (printed p. 62), in the shape the assembly
wants. -/
theorem skewFromSide (G : SimpleGraph V) : Thm106Assembly.SkewFromSide G := by
  intro hG A B C hH _hmax F hF hFne hatt
  exact HyperprismSkewFromSide.admitsBalancedSkewPartition_of_attachments_subset_A
    hG hH hF hFne hatt

/-- **The closing paragraph of the printed proof of 10.6** (printed p. 63), in the shape the
assembly wants.  See the module docstring for the one hypothesis that has to be recovered from
the standing assumption of the preceding paragraph. -/
theorem endgame (G : SimpleGraph V) : Thm106Assembly.Endgame G := by
  intro hG _hK4 A B C hH _hmax hloc
  by_cases hemp : ∃ F : Set V, IsComponent G (HyperprismBasics.hyperVerts A B C)ᶜ F ∧
      F.Nonempty ∧ attachments G F (HyperprismBasics.hyperVerts A B C) = ∅
  · -- *"So we may assume there is no such `F`"*: an attachment-free component has all its
    -- attachments in `A`, so claim (3) applies and gives the third disjunct.
    obtain ⟨F, hF, hFne, hFe⟩ := hemp
    exact Or.inr (Or.inr
      (HyperprismSkewFromSide.admitsBalancedSkewPartition_of_attachments_subset_A hG hH hF hFne
        (by rw [hFe]; exact Set.empty_subset _)))
  · refine HyperprismEndgame.thm_10_6_endgame hG hH ?_ hloc
    intro F hF hFne
    rw [Set.nonempty_iff_ne_empty]
    intro hcon
    exact hemp ⟨F, hF, hFne, hcon⟩

/-- **10.6 from `Claim2` alone.**  The remaining hypothesis is the pp. 60–62 block of the
printed proof; the other two steps are supplied above. -/
theorem thm_10_6_of_claim2 (G : SimpleGraph V) (hG : Berge G) (hK4 : Thm106Assembly.NoK4 G)
    (hclaim2 : Thm106Assembly.Claim2 G)
    (heven : ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃) :
    Thm106Assembly.Thm106Conclusion G :=
  Thm106Assembly.thm_10_6_of_steps G hG hK4 hclaim2 (skewFromSide G) (endgame G) heven

end Workspace.ProofLemmas.Thm106Steps
