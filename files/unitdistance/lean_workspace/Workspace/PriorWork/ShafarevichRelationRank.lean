-- Cited from: I. R. Shafarevich, Extensions with given points of ramification, Publ. Math. IHES 18:71-92, 1963 (English transl. AMS Transl. (2) 59 (1966), 128-149); J. Neukirch, A. Schmidt, K. Wingberg, Cohomology of Number Fields, 2nd ed., Springer, 2008, Chapter X, Section 10.
-- Paper label: Proposition 3.5 (Shafarevich relation-rank estimate) / Proposition A.10
-- NL statement: There is an absolute constant C_0, independent of the field, such that for every totally real cubic number field F (so [F:Q] = 3 and zeta_3 is not in F), the Galois group G = Gal(F^{ur,3}/F) of its maximal everywhere-unramified pro-3 extension satisfies r(G) <= d(G) + C_0.
import Mathlib
import Workspace.Types.ProPGroup
import Workspace.Types.ProPPresentationRank
import Workspace.Types.UnramifiedProPExtension

open scoped NumberField
open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank
open Workspace.Types.UnramifiedProPExtension

/-- **Proposition 3.5 (Shafarevich relation-rank estimate).** There is an absolute constant
`C₀` (independent of `F`) such that for every totally real cubic number field `F`
(`[F : ℚ] = 3`, `F` totally real — so `ζ₃ ∉ F`), the Galois group `G = Gal(F^{ur,3}/F)`
of its maximal everywhere-unramified pro-`3` extension satisfies `r(G) ≤ d(G) + C₀`. -/
axiom ShafarevichRelationRank :
    ∃ C₀ : ℕ, ∀ (F : Type) [Field F] [NumberField F],
      NumberField.IsTotallyReal F → Module.finrank ℚ F = 3 →
        relRank 3 (galUr 3 F) ≤ dRank (galUr 3 F) + (C₀ : ℕ∞)
