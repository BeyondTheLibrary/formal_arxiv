-- Cited from: L. Ribes and P. Zalesskii, Profinite Groups, 2nd ed., Springer, 2010, Section 2.8;
-- H. Koch, Galois Theory of p-Extensions, Springer, 2002, Theorem 4.10; J. D. Dixon, M. P. F. du
-- Sautoy, A. Mann, D. Segal, Analytic Pro-p Groups, 2nd ed., CUP, 1999, Proposition 1.9(ii).
-- Paper label: Proposition 3.3 (second assertion) / Proposition A.8, relation-rank half.
--
-- This is the relation-rank half of `ProPFrattiniQuotientRanks`: if `g_1,…,g_k ∈ Φ(G)` and `N` is
-- the closed normal subgroup they generate, then `r(G/N) ≤ r(G) + k`.  (The generator-rank half
-- `d(G/N) = d(G)` is proved separately in `ProPFrattiniQuotientRanks.lean`.)
--
-- The presentation-lifting argument is carried out in `Workspace.ProofLemmas.ProPRelationRank`:
-- take a minimal pro-p presentation `π : freeProP p d(G) ↠ G` realising `r(G)` relations, lift each
-- `g_i` to `ĝ_i` and adjoin the `ĝ_i` as `k` new relations.  The composite `π' = (G ↠ G/N) ∘ π` is
-- surjective and its kernel `π⁻¹(N)` equals the closed normal closure `M` of the enlarged family:
--   * `M ≤ π⁻¹(N)`: the latter is a closed normal subgroup containing every new relation;
--   * `π⁻¹(N) ≤ M`: `M` is closed in the COMPACT group `freeProP p d`, so `π(M)` is a closed normal
--     subgroup of `G` containing every `g_i`, hence `N ≤ π(M)`; with `ker π ≤ M` this gives the
--     reverse inclusion.
-- Together with the generator-rank half `d(G/N) = d(G)` this presentation witnesses
-- `r(G/N) ≤ r(G) + k`.
import Mathlib
import Workspace.Types.ProPGroup
import Workspace.Types.ProPPresentationRank
import Workspace.ProofLemmas.ProPRelationRank

open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank

/-- **Proposition 3.3 / A.8, relation-rank half.** If `g_1, …, g_k ∈ Φ(G)` and `N` is
the closed normal subgroup they generate, then `r(G/N) ≤ r(G) + k`.  This is the relation-rank
half of `ProPFrattiniQuotientRanks`; the generator-rank half is proved separately. -/
theorem ProPRelationRankFrattiniQuotient (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (hfg : TopFinitelyGenerated G)
    (k : ℕ) (g : Fin k → G) (hg : ∀ i, g i ∈ frattiniOpen G)
    (N : Subgroup G) [N.Normal]
    (hN : N = (Subgroup.normalClosure (Set.range g)).topologicalClosure) :
    relRank p (G ⧸ N) ≤ relRank p G + (k : ℕ∞) :=
  Workspace.ProofLemmas.ProPRelationRank.proPRelationRankFrattiniQuotient
    p G hpro hfg k g hg N hN
