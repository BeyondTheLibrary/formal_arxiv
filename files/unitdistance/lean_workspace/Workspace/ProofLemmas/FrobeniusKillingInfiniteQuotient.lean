import Mathlib
import Workspace.Types.SplittingRamification
import Workspace.Types.FrobeniusSplitting
import Workspace.Types.UnramifiedProPExtension
import Workspace.Types.ProPGroup
import Workspace.Types.ProPPresentationRank
import Workspace.PriorWork.ShafarevichRelationRank
import Workspace.ProofLemmas.ProPFrattiniQuotientRanks
import Workspace.ProofLemmas.ProPBurnsideBasis
import Workspace.ProofLemmas.GolodShafarevichInfinite
import Workspace.ProofLemmas.SublemmaProPQuotientClosed
import Workspace.ProofLemmas.SublemmaTopFinGenQuotientClosed

open scoped NumberField

open Workspace.Types.SplittingRamification
open Workspace.Types.FrobeniusSplitting
open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank

set_option maxHeartbeats 1000000

theorem FrobeniusKillingInfiniteQuotient :
    ∃ L₀ : ℕ, ∀ (F : Type) [Field F] [NumberField F],
      NumberField.IsTotallyReal F → IsGalois ℚ F →
      Module.finrank ℚ F = 3 →
      (¬ ∃ x : F, IsPrimitiveRoot x 3) →
      IsProP 3 (galUr 3 F) →
      TopFinitelyGenerated (galUr 3 F) →
      ∀ ℓ : ℕ, L₀ ≤ ℓ →
        ((ℓ - 1 : ℕ) : ℕ∞) ≤ dRank (galUr 3 F) →
        ∀ (q : Fin ((ℓ - 1) ^ 2 / 100) → ℕ),
          Function.Injective q →
          (∀ b, SplitsCompletelyRat (q b) F) →
          ∀ (σ : (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
                    {v : Ideal (𝓞 F) //
                      v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)}) →
                  galUr 3 F),
            (∀ w, IsFrobeniusRepAt 3 F (σ w) (w.2 : Ideal (𝓞 F))) →
            (∀ w, σ w ∈ frattiniOpen (galUr 3 F)) →
            ∀ (N : Subgroup (galUr 3 F)) [N.Normal],
              N = (Subgroup.normalClosure (Set.range σ)).topologicalClosure →
                Nontrivial (galUr 3 F ⧸ N) ∧
                  Infinite (galUr 3 F ⧸ N) ∧
                  TopFinitelyGenerated (galUr 3 F ⧸ N) ∧
                  IsProP 3 (galUr 3 F ⧸ N) ∧
                  dRank (galUr 3 F ⧸ N) = dRank (galUr 3 F) ∧
                  4 * relRank 3 (galUr 3 F ⧸ N) ≤ (dRank (galUr 3 F ⧸ N)) ^ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  -- Step 0.1: extract the absolute Shafarevich constant `C₀`.
  obtain ⟨C₀, hC₀⟩ := ShafarevichRelationRank
  -- Step 0.3: the threshold `L₀ = max 2 (d₀ + 1)` with `d₀ = 8·C₀ + 6`, uniform in `F`.
  refine ⟨max 2 (8 * C₀ + 6 + 1), ?_⟩
  -- Step 1: introduce all binders.
  intro F _ _ hTR hGal hdeg hnoζ hpro hfg ℓ hℓ hgen q hqinj hqsplit σ hσfrob hσfrat N _ hN
  -- topological-group instance on `G = galUr 3 F` (first conjunct of `IsProP`).
  haveI hTG : IsTopologicalGroup (galUr 3 F) := hpro.1
  -- Step 2: Burnside basis — `d(G)` is the finite natural `d`.
  obtain ⟨hcomm, hpow, d, hdG, hcard⟩ := ProPBurnsideBasis 3 (galUr 3 F) hpro hfg
  -- Step 3: `ℓ - 1 ≤ d`.
  rw [hdG] at hgen
  have hd_ge_l : ℓ - 1 ≤ d := by exact_mod_cast hgen
  -- threshold consequences.
  have h2 : 2 ≤ max 2 (8 * C₀ + 6 + 1) := le_max_left _ _
  have hd0 : 8 * C₀ + 6 + 1 ≤ max 2 (8 * C₀ + 6 + 1) := le_max_right _ _
  -- Step 4: `d ≥ d₀` and `d ≥ 1`.
  have hd_ge_d0 : 8 * C₀ + 6 ≤ d := by omega
  have hd_ge_1 : 1 ≤ d := by omega
  -- Step 5: the index type is `σ`'s domain; establish finiteness and cardinality `3·t`.
  -- each fibre is finite of cardinality 3.
  have hfib : ∀ b : Fin ((ℓ - 1) ^ 2 / 100),
      Nat.card {v : Ideal (𝓞 F) //
          v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)} = 3 := by
    intro b
    have h := (hqsplit b).2.1
    rw [hdeg] at h
    rw [Nat.card_coe_set_eq]; exact h
  have hfin : ∀ b : Fin ((ℓ - 1) ^ 2 / 100),
      Finite {v : Ideal (𝓞 F) //
          v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)} := by
    intro b
    have h := (hqsplit b).2.1
    rw [hdeg] at h
    exact (Set.finite_of_ncard_ne_zero (by rw [h]; norm_num)).to_subtype
  -- `Finite` instance on `σ`'s domain.
  haveI hSfin : Finite (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
      {v : Ideal (𝓞 F) //
        v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)}) := inferInstance
  have hcardS : Nat.card (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
      {v : Ideal (𝓞 F) //
        v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)})
      = 3 * ((ℓ - 1) ^ 2 / 100) := by
    rw [Nat.card_sigma]
    simp only [hfib]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  -- Step 5.3 + Step 6: reindex `σ` by `Fin (Nat.card S)` and restate `N`, keeping the
  -- ORIGINAL `σ` (no `set`, which would introduce a fresh, unrelated `σ`).
  have hrange : Set.range (σ ∘ (Finite.equivFin (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
      {v : Ideal (𝓞 F) //
        v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)})).symm) = Set.range σ := by
    rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
  have hN' : N = (Subgroup.normalClosure
      (Set.range (σ ∘ (Finite.equivFin (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
        {v : Ideal (𝓞 F) //
          v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)})).symm))).topologicalClosure := by
    rw [hrange]; exact hN
  have hg : ∀ i, (σ ∘ (Finite.equivFin (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
      {v : Ideal (𝓞 F) //
        v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)})).symm) i ∈
      frattiniOpen (galUr 3 F) :=
    fun i => hσfrat ((Finite.equivFin (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
      {v : Ideal (𝓞 F) //
        v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)})).symm i)
  -- Step 7: generator and relation ranks of `Ḡ = G ⧸ N`.
  obtain ⟨hdbar, hrbar⟩ :=
    ProPFrattiniQuotientRanks 3 (galUr 3 F) hpro hfg
      (Nat.card (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
        {v : Ideal (𝓞 F) //
          v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)}))
      (σ ∘ (Finite.equivFin (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
        {v : Ideal (𝓞 F) //
          v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)})).symm) hg N hN'
  have hdbar' : dRank (galUr 3 F ⧸ N) = (d : ℕ∞) := hdbar.trans hdG
  -- Step 8a: Shafarevich bound `r(G) ≤ d + C₀`.
  have hrG : relRank 3 (galUr 3 F) ≤ dRank (galUr 3 F) + (C₀ : ℕ∞) := hC₀ F hTR hdeg
  rw [hdG] at hrG
  -- Step 8b: the count bound `100 · t ≤ d²`.
  have htk : 100 * ((ℓ - 1) ^ 2 / 100) ≤ d ^ 2 := by
    have h1 : 100 * ((ℓ - 1) ^ 2 / 100) ≤ (ℓ - 1) ^ 2 := Nat.mul_div_le _ _
    have h2' : (ℓ - 1) ^ 2 ≤ d ^ 2 := Nat.pow_le_pow_left hd_ge_l 2
    omega
  -- Step 8c: relation-rank chain `r(Ḡ) ≤ d + C₀ + 3t`.
  have hr_bound : relRank 3 (galUr 3 F ⧸ N) ≤
      ((d + C₀ + 3 * ((ℓ - 1) ^ 2 / 100) : ℕ) : ℕ∞) := by
    calc relRank 3 (galUr 3 F ⧸ N)
        ≤ (relRank 3 (galUr 3 F)) + ((Nat.card (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
            {v : Ideal (𝓞 F) //
              v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)}) : ℕ) : ℕ∞) := hrbar
      _ ≤ ((d : ℕ∞) + (C₀ : ℕ∞)) + ((Nat.card (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
            {v : Ideal (𝓞 F) //
              v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)}) : ℕ) : ℕ∞) := by gcongr
      _ = ((d + C₀ + 3 * ((ℓ - 1) ^ 2 / 100) : ℕ) : ℕ∞) := by
          rw [hcardS]; push_cast; ring
  -- Step 8d: the ℕ arithmetic core.
  have hquad : 400 * d + 400 * C₀ ≤ 88 * d ^ 2 := by nlinarith [hd_ge_d0]
  have harith : 4 * (d + C₀ + 3 * ((ℓ - 1) ^ 2 / 100)) ≤ d ^ 2 := by
    nlinarith [htk, hquad]
  -- Step 8e: lift the margin to `ℕ∞`.
  have hGS : 4 * relRank 3 (galUr 3 F ⧸ N) ≤ (dRank (galUr 3 F ⧸ N)) ^ 2 := by
    have h4 : 4 * relRank 3 (galUr 3 F ⧸ N) ≤
        4 * ((d + C₀ + 3 * ((ℓ - 1) ^ 2 / 100) : ℕ) : ℕ∞) :=
      mul_le_mul_left' hr_bound 4
    refine le_trans h4 ?_
    rw [hdbar']
    have e1 : (4 : ℕ∞) * ((d + C₀ + 3 * ((ℓ - 1) ^ 2 / 100) : ℕ) : ℕ∞) =
        ((4 * (d + C₀ + 3 * ((ℓ - 1) ^ 2 / 100)) : ℕ) : ℕ∞) := by
      push_cast; ring
    have e2 : ((d : ℕ∞)) ^ 2 = ((d ^ 2 : ℕ) : ℕ∞) := by push_cast; ring
    rw [e1, e2]
    exact_mod_cast harith
  -- Step 9.1: `N` is closed.
  have hNclosed : IsClosed (N : Set (galUr 3 F)) := by
    rw [hN']; exact Subgroup.isClosed_topologicalClosure _
  -- Step 9.2: `Ḡ` is pro-`3`.
  have hproBar : IsProP 3 (galUr 3 F ⧸ N) :=
    SublemmaProPQuotientClosed 3 (galUr 3 F) N hNclosed hpro
  -- Step 9.3: `Ḡ` is topologically finitely generated.
  have hfgBar : TopFinitelyGenerated (galUr 3 F ⧸ N) :=
    SublemmaTopFinGenQuotientClosed (galUr 3 F) N hfg
  -- Step 10: `Ḡ` is nontrivial.
  obtain ⟨_, _, d', hd'bar, hcard'⟩ := ProPBurnsideBasis 3 (galUr 3 F ⧸ N) hproBar hfgBar
  have hdd' : d' = d := by
    have : (d' : ℕ∞) = (d : ℕ∞) := hd'bar.symm.trans hdbar'
    exact_mod_cast this
  have hd'ge1 : 1 ≤ d' := by omega
  have hfrat_fin :
      Finite ((galUr 3 F ⧸ N) ⧸ frattiniOpen (galUr 3 F ⧸ N)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard']; positivity)
  have hgt : 1 < Nat.card ((galUr 3 F ⧸ N) ⧸ frattiniOpen (galUr 3 F ⧸ N)) := by
    rw [hcard']
    calc 1 < 3 ^ 1 := by norm_num
      _ ≤ 3 ^ d' := Nat.pow_le_pow_right (by norm_num) hd'ge1
  haveI : Finite ((galUr 3 F ⧸ N) ⧸ frattiniOpen (galUr 3 F ⧸ N)) := hfrat_fin
  haveI hntFrat : Nontrivial ((galUr 3 F ⧸ N) ⧸ frattiniOpen (galUr 3 F ⧸ N)) :=
    Finite.one_lt_card_iff_nontrivial.mp hgt
  -- Derive nontriviality of `Ḡ` from the coset projection (no `Normal` instance needed).
  have hntBar : Nontrivial (galUr 3 F ⧸ N) :=
    (QuotientGroup.mk_surjective (s := frattiniOpen (galUr 3 F ⧸ N))).nontrivial
  -- Step 11: `Ḡ` is infinite.
  have hinfBar : Infinite (galUr 3 F ⧸ N) :=
    GolodShafarevichInfinite 3 (galUr 3 F ⧸ N) hproBar hfgBar hntBar hGS
  -- Step 12: assemble.
  exact ⟨hntBar, hinfBar, hfgBar, hproBar, hdbar, hGS⟩
