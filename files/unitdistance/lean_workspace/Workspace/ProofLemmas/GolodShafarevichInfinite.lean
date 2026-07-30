-- Proposition 3.4 (contrapositive form) / Proposition A.9.
-- Derived as the pure contrapositive of the Golod-Shafarevich inequality
-- (`Workspace.ProofLemmas.GolodShafarevichInequality`): a nontrivial finitely
-- generated pro-p group with 4 r(G) <= d(G)^2 is infinite.
import Mathlib
import Workspace.Types.ProPGroup
import Workspace.Types.ProPPresentationRank
import Workspace.ProofLemmas.GolodShafarevichInequality

open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank

set_option maxHeartbeats 800000

/-- **Proposition 3.4 (Golod–Shafarevich, contrapositive).** A nontrivial finitely generated
pro-`p` group with `4·r(G) ≤ d(G)^2` is infinite. -/
theorem GolodShafarevichInfinite (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (hfg : TopFinitelyGenerated G) (hnt : Nontrivial G)
    (hgs : 4 * relRank p G ≤ (dRank G) ^ 2) : Infinite G := by
  rw [← not_finite_iff_infinite]
  intro hfin
  have h := GolodShafarevichInequality p G hpro hfg hfin hnt
  exact lt_irrefl _ (lt_of_lt_of_le h hgs)
