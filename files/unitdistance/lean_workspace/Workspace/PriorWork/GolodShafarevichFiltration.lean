-- Cited from: E. S. Golod and I. R. Shafarevich, On the class field tower, Izv. Akad. Nauk SSSR
-- Ser. Mat. 28(2):261-272, 1964; H. Koch, Galois Theory of p-Extensions, Springer, 2002, Ch. 11
-- (the filtration inequality for the augmentation ideal of the completed group algebra).
-- Paper label: Proposition 3.4 / Proposition A.9 (technical core)
--
-- The cited result was
--   d(G)² < 4·r(G)   for a finite nontrivial finitely generated pro-p group G.
-- The generating-function deduction is proved from Mathlib in
-- `Workspace.ProofLemmas.GolodShafarevichCore.gs_core`: from `c 0 = 1`, `c 1 = d`, the inequality
-- `d·c(n+1) ≤ c(n+2) + r·c n` and eventual vanishing of `c`, one gets `d² < 4r` by summing against
-- `t₀ⁿ⁺²` at the positive root `t₀` of `r t² − d t + 1`.
--
-- What remains admitted is exactly the module-theoretic input: the Hilbert function
--   c n  =  dim_{𝔽_p} (Iⁿ / Iⁿ⁺¹)
-- of the augmentation ideal `I` of `𝔽_p[G]` satisfies `c 0 = 1`, `c 1 = d(G)`, the filtration
-- inequality with `r = r(G)` (this comes from the minimal free presentation
-- `Ω^r → Ω^d → Ω → 𝔽_p → 0` of the completed group algebra), and vanishes eventually because `I` is
-- nilpotent for finite `G`.  Mathlib has neither the completed group algebra of a pro-p group nor
-- this filtration estimate.
--
-- NL statement: For a finite nontrivial topologically finitely generated pro-p group G with
-- generator rank d and relation rank r, there is a sequence c : ℕ → ℕ (the dimensions of the
-- successive quotients of the augmentation filtration of 𝔽_p[G]) with c 0 = 1, c 1 = d,
-- d * c (n+1) ≤ c (n+2) + r * c n for all n, and c n = 0 for all large n.
import Mathlib
import Workspace.Types.ProPGroup
import Workspace.Types.ProPPresentationRank

open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank

/-- **Golod–Shafarevich filtration inequality.**  The Hilbert function of the
augmentation filtration of `𝔽_p[G]` exists with the stated properties. -/
axiom GolodShafarevichFiltration (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (hfg : TopFinitelyGenerated G) (hfin : Finite G) (hnt : Nontrivial G)
    (d r : ℕ) (hd : (d : ℕ∞) = dRank G) (hr : (r : ℕ∞) = relRank p G) :
    ∃ c : ℕ → ℕ, c 0 = 1 ∧ c 1 = d ∧
      (∀ n, d * c (n + 1) ≤ c (n + 2) + r * c n) ∧
      (∃ N, ∀ n, N ≤ n → c n = 0)
