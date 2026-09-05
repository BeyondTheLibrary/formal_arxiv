import Mathlib
import Workspace.Types.Core
import Workspace.Types.Knots
import Workspace.ProofLemmas.KnotFromTwist
import Workspace.ProofLemmas.StriationCompl

/-!
# Striation bookkeeping for the closing paragraph of 9.4
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm94ClosingStriation

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **PAPER (9.4, printed p. 52):** *"Now `T₁,T₂` agree on `S₁`, and so there is some
`Sᵢ` on which they disagree."*

The same statement without choosing orientations says that any two distinct antistrips and any
fixed strip occur together in a twist with some other strip. -/
theorem exists_twist_with_fixed_strip {G : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (hL : IsStriation G S T) (i : Fin m) {j j' : Fin n} (hjj' : j ≠ j') :
    ∃ i' : Fin m, i ≠ i' ∧ IsTwist G (S i) (S i') (T j) (T j') := by
  have hLc : IsStriation Gᶜ T S :=
    Workspace.ProofLemmas.StriationCompl.isStriation_compl hL
  obtain ⟨hTc, hSc, -, -, -, -, -, -, -, -, -, hpcC, htwC, -⟩ := hLc
  have htw0 : ∃ a b : Fin m, a ≠ b ∧ IsTwist Gᶜ (T j) (T j') (S a) (S b) := by
    rcases lt_trichotomy j j' with hlt | heq | hgt
    · exact htwC j j' hlt
    · exact absurd heq hjj'
    · obtain ⟨a, b, hab, htw⟩ := htwC j' j hgt
      refine ⟨a, b, hab, ?_⟩
      simp only [IsTwist, AgreeOn] at htw ⊢
      tauto
  let Ag : Fin m → Prop := fun k => AgreeOn Gᶜ (T j) (T j') (S k)
  let Ds : Fin m → Prop := fun k =>
    (ParallelStripAntistrip Gᶜ (T j) (S k) ∧ CoParallel Gᶜ (T j') (S k)) ∨
      (CoParallel Gᶜ (T j) (S k) ∧ ParallelStripAntistrip Gᶜ (T j') (S k))
  have hstatus : ∀ k : Fin m, Ag k ∨ Ds k := by
    intro k
    rcases hpcC j k with hj | hj <;> rcases hpcC j' k with hj' | hj'
    · exact Or.inl (Or.inl ⟨hj, hj'⟩)
    · exact Or.inr (Or.inl ⟨hj, hj'⟩)
    · exact Or.inr (Or.inr ⟨hj, hj'⟩)
    · exact Or.inl (Or.inr ⟨hj, hj'⟩)
  have hnotBoth : ∀ k : Fin m, ¬ (Ag k ∧ Ds k) := by
    intro k h
    have hn1 := Workspace.ProofLemmas.StriationCompl.not_parallel_and_coParallel
      (G := Gᶜ) (hTc j) (hSc k)
    have hn2 := Workspace.ProofLemmas.StriationCompl.not_parallel_and_coParallel
      (G := Gᶜ) (hTc j') (hSc k)
    simp only [Ag, Ds, AgreeOn] at h
    tauto
  obtain ⟨a, b, hab, htw⟩ := htw0
  have htw' : (Ag a ∧ Ds b) ∨ (Ag b ∧ Ds a) := by
    simpa only [Ag, Ds, IsTwist] using htw
  obtain ⟨k, hik, htwik⟩ : ∃ k : Fin m, i ≠ k ∧ IsTwist Gᶜ (T j) (T j') (S i) (S k) := by
    rcases htw' with ⟨ha, hb⟩ | ⟨hb, ha⟩ <;> rcases hstatus i with hi | hi
    · refine ⟨b, ?_, Or.inl ⟨hi, hb⟩⟩
      intro h
      subst b
      exact hnotBoth i ⟨hi, hb⟩
    · refine ⟨a, ?_, Or.inr ⟨ha, hi⟩⟩
      intro h
      subst a
      exact hnotBoth i ⟨ha, hi⟩
    · refine ⟨a, ?_, Or.inl ⟨hi, ha⟩⟩
      intro h
      subst a
      exact hnotBoth i ⟨hi, ha⟩
    · refine ⟨b, ?_, Or.inr ⟨hb, hi⟩⟩
      intro h
      subst b
      exact hnotBoth i ⟨hb, hi⟩
  refine ⟨k, hik, ?_⟩
  exact (Workspace.ProofLemmas.StriationCompl.isTwist_compl
    (hL.1 i) (hL.1 k) (hL.2.1 j) (hL.2.1 j')
    (hL.2.2.2.2.1 i j) (hL.2.2.2.2.1 i j')
    (hL.2.2.2.2.1 k j) (hL.2.2.2.2.1 k j')
    (hL.2.2.2.2.2.2.2.2.2.2.2.1 i j)
    (hL.2.2.2.2.2.2.2.2.2.2.2.1 i j')
    (hL.2.2.2.2.2.2.2.2.2.2.2.1 k j)
    (hL.2.2.2.2.2.2.2.2.2.2.2.1 k j')).mp htwik

end Workspace.ProofLemmas.Thm94ClosingStriation
