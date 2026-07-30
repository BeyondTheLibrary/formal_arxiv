import Mathlib
import Workspace.Types.PlanarCounting
import Workspace.Types.SplittingRamification
import Workspace.Types.DiscriminantsClassNumber
import Workspace.Types.CMAdjoinI
import Workspace.Types.AdmissibleDatum
import Workspace.Types.ProPGroup
import Workspace.Types.ProPPresentationRank
import Workspace.Types.CyclotomicCharacterFields
import Workspace.Types.FrobeniusSplitting
import Workspace.Types.MinkowskiWindow
import Workspace.Types.UnramifiedProPExtension
import Workspace.ProofLemmas.Theorem23GeometricCriterion
import Workspace.ProofLemmas.Prop38FieldConstruction
import Workspace.ProofLemmas.SublemmaCMModelExists

/-!
# Main theorem file — "Planar Point Sets with Many Unit Distances"

Contains the proven main theorem `theorem_1_1_unit_distance` (Theorem 1.1), stated
against the accepted type interfaces.  Its proof is complete (no `sorry`); the supporting
propositions, lemmas, and prior-work facts have been factored out into
`Workspace/ProofLemmas/` and are cited here by name.
-/

open scoped NumberField
open Workspace.Types.PlanarCounting
open Workspace.Types.SplittingRamification
open Workspace.Types.DiscriminantsClassNumber
open Workspace.Types.CMAdjoinI
open Workspace.Types.AdmissibleDatum
open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank
open Workspace.Types.CyclotomicCharacterFields
open Workspace.Types.FrobeniusSplitting
open Workspace.Types.MinkowskiWindow
open Workspace.Types.UnramifiedProPExtension

namespace Workspace.MainTheorem

/-! ## Theorem 1.1 — the main theorem -/

/-- **Theorem 1.1 (Main Theorem).** There is an absolute constant `δ > 0` such that for
every `N` there is an integer `n ≥ N` (with `n ≥ 1`) for which the maximum number of unit
distances among `n` planar points satisfies `ν(n) ≥ n^{1+δ}`.  (Equivalently: infinitely
many `n` with `ν(n) ≥ n^{1+δ}`.) -/
theorem theorem_1_1_unit_distance :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧
      (nuMax n : ℝ) ≥ (n : ℝ) ^ ((1 : ℝ) + δ) := by
  obtain ⟨C, hC, C', hC', L₀, hL₀, hmain⟩ := Prop38FieldConstruction
  set ℓ := max L₀ 11 with hℓ_def
  have hℓ : L₀ ≤ ℓ := le_max_left _ _
  have h11 : 11 ≤ ℓ := le_max_right _ _
  have hsq : 100 ≤ (ℓ - 1) ^ 2 := by
    have h10 : 10 ≤ ℓ - 1 := by omega
    calc (100 : ℕ) = 10 ^ 2 := by norm_num
      _ ≤ (ℓ - 1) ^ 2 := Nat.pow_le_pow_left h10 2
  have ht : 0 < (ℓ - 1) ^ 2 / 100 := by omega
  obtain ⟨F, instF, instNF, q, Fj, H, hP1, hP2, hprimes, hlayer, hP5, hP6⟩ := hmain ℓ hℓ
  choose finFj nfFj hbody using hlayer
  have hcm : ∀ j, ∃ (K : Type) (_ : Field K) (_ : NumberField K)
      (_ : Algebra (↥(Fj j)) K), IsAdjoinI (↥(Fj j)) K := by
    intro j
    haveI := nfFj j
    haveI : NumberField.IsTotallyReal (↥(Fj j)) := (hbody j).2.2.2.1
    exact SublemmaCMModelExists (↥(Fj j))
  choose Kj fieldKj nfKj algKj hadjKj using hcm
  let data : ℕ → AdmissibleDatum := fun j =>
    { L := ↥(Fj j)
      K := Kj j
      fieldL := inferInstance
      fieldK := fieldKj j
      nfL := nfFj j
      nfK := nfKj j
      trL := (hbody j).2.2.2.1
      algLK := algKj j
      h_adjoin := hadjKj j
      t := (ℓ - 1) ^ 2 / 100
      ht := ht
      q := q
      hq_prime := hprimes.2
      hq_distinct := hprimes.1
      hq_mod4 := fun b => ((hbody j).2.2.2.2.2.1 b).1
      hq_split := fun b => ((hbody j).2.2.2.2.2.1 b).2 }
  have hdeg : Filter.Tendsto (fun j => deg (data j)) Filter.atTop Filter.atTop := hP2.2.2
  have hclass : ∀ j, (classNumber (data j).K : ℝ) ≤ H ^ (deg (data j)) := by
    intro j
    exact ((hbody j).2.2.2.2.2.2 (Kj j) (fieldKj j) (nfKj j) (algKj j) (hadjKj j)).2
  exact Theorem23GeometricCriterion ((ℓ - 1) ^ 2 / 100) ht q data
    (fun j => rfl) (fun j => HEq.rfl) hdeg H hP5.1 hclass hP6

end Workspace.MainTheorem
