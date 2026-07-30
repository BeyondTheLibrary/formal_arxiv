import Mathlib
import Workspace.Types.AdmissibleDatum
import Workspace.Types.DiscriminantsClassNumber
import Workspace.Types.CMAdjoinI
import Workspace.ProofLemmas.Fact215ConjugatePrimePairs
import Workspace.ProofLemmas.ConjugatePairIndexing
import Workspace.ProofLemmas.IdealClassPigeonholeFiber
import Workspace.ProofLemmas.PrincipalGeneratorOfClassEquality
import Workspace.ProofLemmas.ConjQuotientRelNormOne
import Workspace.ProofLemmas.ConjQuotientUnitModulus
import Workspace.ProofLemmas.QSquaredClearsConjQuotient
import Workspace.ProofLemmas.ValuationVectorInjective
import Workspace.ProofLemmas.FiberCountToExpBound

open scoped NumberField nonZeroDivisors
open Workspace.Types.DiscriminantsClassNumber
open Workspace.Types.CMAdjoinI
open Workspace.Types.AdmissibleDatum

set_option maxHeartbeats 4000000

theorem Prop22NormOneElements (d : AdmissibleDatum) (H : ℝ) (hH : 0 < H)
    (hclass : (classNumber d.K : ℝ) ≤ H ^ (deg d)) :
    ∃ U : Finset d.K,
      (∀ u ∈ U, IsIntegral ℤ ((Dq d : d.K) * u)) ∧
      (∀ u ∈ U, relNorm_KL d.h_adjoin u = 1) ∧
      (∀ u ∈ U, ∀ σ : d.K →+* ℂ, ‖σ u‖ = 1) ∧
      (U.card : ℝ) ≥ Real.exp (((d.t : ℝ) * Real.log 2 - Real.log H) * (deg d : ℝ)) := by
  classical
  -- Step 0: the conjugate-pair family
  obtain ⟨P, Pc, bidx, S, hswap, hinj, hram, hSset, hScard, hSeq, htrans⟩ :=
    ConjugatePairIndexing d (Fact215ConjugatePrimePairs d)
  -- the family-property block consumed by the downstream sublemmas
  have hfam := And.intro hswap (And.intro hinj (And.intro hram htrans))
  -- Step 1: the ideals A_δ
  set A : (Fin (d.t * deg d) → Bool) → Ideal (𝓞 d.K) :=
    fun δ => ∏ s, if δ s then (P s).asIdeal else (Pc s).asIdeal with hAdef
  have hAne : ∀ δ, A δ ≠ 0 := by
    intro δ
    rw [hAdef]
    simp only
    rw [Finset.prod_ne_zero_iff]
    intro s _
    by_cases hδ : δ s
    · simp only [hδ, if_true]; exact (P s).ne_bot
    · simp only [hδ, if_false]; exact (Pc s).ne_bot
  -- the class map
  set Φ : (Fin (d.t * deg d) → Bool) → ClassGroup (𝓞 d.K) :=
    fun δ => ClassGroup.mk0 ⟨A δ, mem_nonZeroDivisors_of_ne_zero (hAne δ)⟩ with hΦdef
  -- Step 1: pigeonhole
  obtain ⟨η, hηprod, hηreal⟩ := IdealClassPigeonholeFiber Φ
  set F : Finset (Fin (d.t * deg d) → Bool) :=
    Finset.univ.filter (fun ε => Φ ε = Φ η) with hFdef
  -- Step 2: generators α_ε for ε ∈ F
  have hgen : ∀ ε ∈ F, ∃ α : d.K, α ≠ 0 ∧
      FractionalIdeal.spanSingleton (𝓞 d.K)⁰ α
        = (↑(A ε) : FractionalIdeal (𝓞 d.K)⁰ d.K) *
          (↑(A η) : FractionalIdeal (𝓞 d.K)⁰ d.K)⁻¹ := by
    intro ε hε
    have hΦ : Φ ε = Φ η := (Finset.mem_filter.mp hε).2
    exact PrincipalGeneratorOfClassEquality d.K (A ε) (A η) (hAne ε) (hAne η) hΦ
  -- the conjugate-quotient map
  set u : (Fin (d.t * deg d) → Bool) → d.K :=
    fun ε => if hε : ε ∈ F then
      (Classical.choose (hgen ε hε)) / conjAut d.h_adjoin (Classical.choose (hgen ε hε))
    else 0 with hudef
  have hu : ∀ ε ∈ F, ∃ α : d.K, α ≠ 0 ∧ u ε = α / conjAut d.h_adjoin α ∧
      FractionalIdeal.spanSingleton (𝓞 d.K)⁰ α
        = (↑(A ε) : FractionalIdeal (𝓞 d.K)⁰ d.K) *
          (↑(A η) : FractionalIdeal (𝓞 d.K)⁰ d.K)⁻¹ := by
    intro ε hε
    refine ⟨Classical.choose (hgen ε hε), (Classical.choose_spec (hgen ε hε)).1, ?_,
      (Classical.choose_spec (hgen ε hε)).2⟩
    rw [hudef]; simp only [hε, dif_pos]
  refine ⟨F.image u, ?_, ?_, ?_, ?_⟩
  · -- integrality
    intro v hv
    obtain ⟨ε, hε, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨α, hα, hue, hspan⟩ := hu ε hε
    rw [hue]
    exact QSquaredClearsConjQuotient d P Pc bidx hfam η ε α hα hspan
  · -- relative norm one
    intro v hv
    obtain ⟨ε, hε, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨α, hα, hue, hspan⟩ := hu ε hε
    rw [hue]
    exact ConjQuotientRelNormOne d.h_adjoin α hα
  · -- unit modulus
    intro v hv σ
    obtain ⟨ε, hε, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨α, hα, hue, hspan⟩ := hu ε hε
    rw [hue]
    exact ConjQuotientUnitModulus d.h_adjoin σ α hα
  · -- count bound
    have hInj : Set.InjOn u ↑F :=
      ValuationVectorInjective d P Pc bidx hfam η F u hu
    have hcardU : (F.image u).card = F.card := Finset.card_image_of_injOn hInj
    have hFcard : F.card = Fintype.card {x : (Fin (d.t * deg d) → Bool) // Φ x = Φ η} := by
      rw [hFdef]; exact (Fintype.card_subtype _).symm
    have hcardD : Fintype.card (Fin (d.t * deg d) → Bool) = 2 ^ (d.t * deg d) := by
      simp [Fintype.card_fun]
    have hcardC : Fintype.card (ClassGroup (𝓞 d.K)) = classNumber d.K := rfl
    have hh : 0 < classNumber d.K := by
      rw [← hcardC]; exact Fintype.card_pos
    have hfiber : ((2 : ℝ) ^ (d.t * deg d)) / (classNumber d.K : ℝ) ≤ (F.card : ℝ) := by
      rw [hFcard]
      have hthis := hηreal
      rw [hcardD, hcardC] at hthis
      exact_mod_cast hthis
    have hbound := FiberCountToExpBound d H hH F.card hh hfiber hclass
    rw [ge_iff_le, hcardU]
    exact hbound

