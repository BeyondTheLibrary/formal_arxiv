import Mathlib
import Workspace.Types.BinVec
import Workspace.Types.DelProb
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.LengthsOnlyProcess
import Workspace.Types.AlternatingSumExpression

open Workspace.Types.BinVec
open Workspace.Types.PartialDeletionProcess
open Workspace.Types.LengthsOnlyProcess
open Workspace.Types.AlternatingSumExpression

open scoped BigOperators

set_option linter.dupNamespace false

/-!
# SignedInnerDefs — shared low-level defs `signedInner` and `sigmaSet`

These two definitions were relocated here (keeping their fully-qualified
names in namespace `Workspace.ProofLemmas.LengthsDiffBoundedByAltSum`) to
break the import cycle between `Path4Assembly` and
`LengthsDiffBoundedByAltSum`.  Both files now import this module for the two
defs instead of importing each other for them.
-/

namespace Workspace.ProofLemmas.LengthsDiffBoundedByAltSum

/-- The signed inner integrand for a same-parity middle mask `m` at offset `r`
and prefix/suffix lengths `z₋ = p.1`, `z₊ = p.2`: the offset/prefix/suffix
weights times the SIGNED closed form (window-parity sign · `Q`-selector ·
`∏ ellFactor`) of `InnerSumSignedClosedForm`.  This is *exactly* the integrand
of `LengthsDiffTsumSignedRSum`'s RHS; abbreviating it keeps the statements
readable. -/
noncomputable def signedInner (n : ℕ) (δ : Workspace.Types.DelProb.DelProb)
    (m : Workspace.Types.BinVec.BinVec (n / 2)) (p : ℕ × ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
    (offsetWeight n r).toReal *
      (prefixLengthWeight n δ r p.1).toReal *
      (suffixLengthWeight n δ r p.2).toReal *
      (let Q_e : ℝ :=
          ∏ j ∈ (Finset.univ.filter
                   (fun j : Fin (n / 2) => ((n / 4 : ℤ) + r + (j : ℕ)) % 2 = 0)),
            (1 - ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹))
        let Q_o : ℝ :=
          ∏ j ∈ (Finset.univ.filter
                   (fun j : Fin (n / 2) => ((n / 4 : ℤ) + r + (j : ℕ)) % 2 = 1)),
            (1 - ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹))
        if h : ((Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)).Nonempty then
            (-1 : ℝ) ^ (((n / 4 : ℤ) + r + ((((Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)).min' h : Fin (n / 2)) : ℕ)) % 2).toNat *
              (if ((n / 4 : ℤ) + r + ((((Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)).min' h : Fin (n / 2)) : ℕ)) % 2 = 0
               then Q_e else Q_o) *
              (∏ j ∈ ((Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)), ellFactor n ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) r (j : ℕ))
          else Q_e - Q_o)

/-- The `σ`-set `{j+1 : m.bit j = true}` — the paper's location set in
`{1,…,n/2}` for the middle mask `m`.  This is the `ℓ` argument that
`AltSumExpansionMatches` feeds to `altRSum`. -/
noncomputable def sigmaSet (n : ℕ) (m : Workspace.Types.BinVec.BinVec (n / 2)) : Finset ℕ :=
  ((Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)).image
    (fun j => j.val + 1)

end Workspace.ProofLemmas.LengthsDiffBoundedByAltSum
