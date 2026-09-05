import Workspace.Types.Core
import Workspace.ProofLemmas.PerfectBlockOneBoundaryPalette
import Workspace.ProofLemmas.PerfectBlockEvenMarkerPalette
import Workspace.ProofLemmas.PerfectBlockOddMarkerPalette

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas

open Workspace.Types.Core

/-- A perfect marker-path block admits colorings whose boundary palettes have
the exact sizes, and the parity-controlled overlap, required for two-join
coloring assembly. -/
theorem PerfectMarkerBlockControlledPaletteColoring
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W)
    (X A B : Set W)
    (hA : A ⊆ X) (hB : B ⊆ X) (hAB : Disjoint A B)
    (P : List W) (pA pB : W)
    (hP : SPGT.IsPathFrom K P pA pB)
    (hPpos : 1 ≤ SPGT.pathLength P)
    (hPX : Disjoint X {v : W | v ∈ P})
    (hpA : ∀ x ∈ X, K.Adj pA x ↔ x ∈ A)
    (hpB : ∀ x ∈ X, K.Adj pB x ↔ x ∈ B)
    (hinternal : ∀ v ∈ SPGT.interior P, ∀ x ∈ X, ¬ K.Adj v x)
    (hperfect : SPGT.IsPerfect (K.induce (X ∪ {v : W | v ∈ P})))
    (T : Set W) (hT : T ⊆ X) (n : ℕ) :
    (∀ C : Set W, C = A ∨ C = B →
      let c := (K.induce (C ∩ T)).cliqueNum
      c ≤ n → (K.induce T).cliqueNum ≤ n →
        ∃ col : (K.induce T).Coloring (Fin n),
          (col '' {v : T | (v : W) ∈ C}).ncard = c) ∧
    ((K.induce (T ∪ {v : W | v ∈ P})).cliqueNum ≤ n →
      let a := (K.induce (A ∩ T)).cliqueNum
      let b := (K.induce (B ∩ T)).cliqueNum
      ∃ col : (K.induce T).Coloring (Fin n),
        let PA : Set (Fin n) := col '' {v : T | (v : W) ∈ A}
        let PB : Set (Fin n) := col '' {v : T | (v : W) ∈ B}
        PA.ncard = a ∧ PB.ncard = b ∧
          (Odd (SPGT.pathLength P) → (PA ∩ PB).ncard = a + b - n) ∧
          (Even (SPGT.pathLength P) → (PA ∩ PB).ncard = min a b)) := by
  constructor
  · intro C hC c hc hTn
    exact PerfectBlockOneBoundaryPalette K X A B hA hB hAB P pA pB hP hPpos hPX
      hpA hpB hinternal hperfect T hT n C hC hc hTn
  · intro hn a b
    rcases Nat.even_or_odd (SPGT.pathLength P) with hpar | hpar
    · obtain ⟨col, h1, h2, h3⟩ :=
        PerfectBlockEvenMarkerPalette K X A B hA hB hAB P pA pB hP hPpos hPX
          hpA hpB hinternal hperfect T hT n hn hpar
      refine ⟨col, h1, h2, ?_, ?_⟩
      · intro hodd
        exact absurd hpar (Nat.not_even_iff_odd.mpr hodd)
      · intro _
        exact h3
    · obtain ⟨col, h1, h2, h3⟩ :=
        PerfectBlockOddMarkerPalette K X A B hA hB hAB P pA pB hP hPpos hPX
          hpA hpB hinternal hperfect T hT n hn hpar
      refine ⟨col, h1, h2, ?_, ?_⟩
      · intro _
        exact h3
      · intro heven
        exact absurd hpar (Nat.not_odd_iff_even.mpr heven)

end Workspace.ProofLemmas
