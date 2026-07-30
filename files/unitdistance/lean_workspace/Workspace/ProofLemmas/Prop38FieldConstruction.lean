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
import Workspace.ProofLemmas.Prop38BaseFieldConstruction
import Workspace.ProofLemmas.GalUrIsProP
import Workspace.ProofLemmas.GalUrGeneratorLowerBound
import Workspace.ProofLemmas.BaseRootDiscriminantBound
import Workspace.ProofLemmas.FrobeniusKillingInfiniteQuotient
import Workspace.ProofLemmas.UnramifiedProPTowerFields
import Workspace.ProofLemmas.TowerLayerProperties
import Workspace.ProofLemmas.CMModelDiscriminantClassNumberBounds
import Workspace.ProofLemmas.FieldConstructionNumericBounds
import Workspace.ProofLemmas.Prop36ChebotarevApplication
import Workspace.ProofLemmas.GalUrTopFinGen
import Workspace.ProofLemmas.UnramifiedProPTowerCorrespondence
import Workspace.ProofLemmas.ProPBurnsideBasis
import Workspace.ProofLemmas.ProPFrattiniQuotientRanks
import Workspace.ProofLemmas.GolodShafarevichInequality
import Workspace.ProofLemmas.GolodShafarevichInfinite
import Workspace.PriorWork.ShafarevichRelationRank
import Workspace.ProofLemmas.ClassNumberRootDiscriminantBound
import Workspace.ProofLemmas.PrimesOneModThreeLogSum

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

theorem Prop38FieldConstruction :
    ∃ C : ℝ, 0 < C ∧ ∃ C' : ℝ, 0 < C' ∧ ∃ L₀ : ℕ, 0 < L₀ ∧
      ∀ ℓ : ℕ, L₀ ≤ ℓ →
        ∃ (F : Type) (_ : Field F) (_ : NumberField F)
          (q : Fin ((ℓ - 1) ^ 2 / 100) → ℕ)
          (Fj : ℕ → IntermediateField F (AlgebraicClosure F))
          (H : ℝ),
          -- (P1)
          (NumberField.IsTotallyReal F ∧ IsGalois ℚ F ∧ Module.finrank ℚ F = 3 ∧
            (¬ ∃ x : F, IsPrimitiveRoot x 3) ∧
            Real.log (rootDiscriminant F) ≤ C * (ℓ : ℝ) * Real.log (ℓ : ℝ)) ∧
          -- (P2): tower base, strictly increasing, degrees → ∞
          (Fj 0 = ⊥ ∧ StrictMono Fj ∧
            Filter.Tendsto (fun j => Module.finrank ℚ ↥(Fj j)) Filter.atTop Filter.atTop) ∧
          -- primes: distinct and prime
          (Function.Injective q ∧ ∀ b, (q b).Prime) ∧
          -- per-layer properties (P2 layer data, P3, P4, P5 body)
          (∀ j, ∃ (_ : FiniteDimensional F ↥(Fj j)) (_ : NumberField ↥(Fj j)),
            IsGalois F ↥(Fj j) ∧
            EverywhereUnramified F ↥(Fj j) ∧
            IsPGroup 3 (↥(Fj j) ≃ₐ[F] ↥(Fj j)) ∧
            NumberField.IsTotallyReal ↥(Fj j) ∧
            rootDiscriminant ↥(Fj j) = rootDiscriminant F ∧
            (∀ b, q b % 4 = 1 ∧ SplitsCompletelyRat (q b) ↥(Fj j)) ∧
            (∀ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra ↥(Fj j) K),
              IsAdjoinI ↥(Fj j) K →
                rootDiscriminant K ≤ 2 * rootDiscriminant F ∧
                (classNumber K : ℝ) ≤ H ^ (Module.finrank ℚ ↥(Fj j)))) ∧
          -- (P5) tail: bound on H_ℓ
          (0 < H ∧ Real.log H ≤ C' * (ℓ : ℝ) * Real.log (ℓ : ℝ)) ∧
          -- (P6)
          (0 < (((ℓ - 1) ^ 2 / 100 : ℕ) : ℝ) * Real.log 2 - Real.log H) := by
  -- ===== Step 1: absolute constants =====
  obtain ⟨Cclass, hCclass_pos, hClass⟩ := ClassNumberRootDiscriminantBound
  obtain ⟨C_D, hC_D_pos, ℓ₀_D, hD_body⟩ := BaseRootDiscriminantBound
  obtain ⟨C', hC'_pos, L₀_I, hL₀_I_pos, hI_body⟩ :=
    FieldConstructionNumericBounds Cclass hCclass_pos C_D hC_D_pos
  obtain ⟨L₀_E, hE⟩ := FrobeniusKillingInfiniteQuotient
  refine ⟨C_D, hC_D_pos, C', hC'_pos, max (max (max ℓ₀_D L₀_I) L₀_E) 11, ?_, ?_⟩
  · have h11 : (11 : ℕ) ≤ max (max (max ℓ₀_D L₀_I) L₀_E) 11 := le_max_right _ _
    omega
  intro ℓ hℓ
  -- threshold clauses
  have h1 : max (max ℓ₀_D L₀_I) L₀_E ≤ ℓ := le_trans (le_max_left _ 11) hℓ
  have h2 : max ℓ₀_D L₀_I ≤ ℓ := le_trans (le_max_left _ L₀_E) h1
  have hℓ0D : ℓ₀_D ≤ ℓ := le_trans (le_max_left _ L₀_I) h2
  have hL0I : L₀_I ≤ ℓ := le_trans (le_max_right ℓ₀_D _) h2
  have hL0E : L₀_E ≤ ℓ := le_trans (le_max_right _ L₀_E) h1
  have hℓ11 : 11 ≤ ℓ := le_trans (le_max_right _ 11) hℓ
  have hℓ2 : 2 ≤ ℓ := by omega
  have ht_pos : 0 < (ℓ - 1) ^ 2 / 100 := by
    have h10 : 10 ≤ ℓ - 1 := by omega
    have : 100 ≤ (ℓ - 1) ^ 2 := by nlinarith
    omega
  -- ===== Step 2: base field package (Group A) =====
  obtain ⟨r, hr_mono, hp, hm, hskip, D, hD_prod, chi, hchi_ord, hchi_cond,
      Fbase, Mbase, hF_eq, hM_eq, hFM_le, nfF, nfM, algFM,
      hst, hTR, hGal, hdeg, hno, hUnr, hGalM_iso, hDF, M', hM'fin, hM'iso⟩ :=
    Prop38BaseFieldConstruction ℓ hℓ2
  haveI : NumberField (↥Fbase) := nfF
  -- pro-3, top-fin-gen
  have hpro : IsProP 3 (galUr 3 (↥Fbase)) := GalUrIsProP (↥Fbase)
  have hfg : TopFinitelyGenerated (galUr 3 (↥Fbase)) := GalUrTopFinGen (↥Fbase) hTR hdeg
  -- ===== Step 3: generator lower bound (Group C) =====
  obtain ⟨φ⟩ := hM'iso
  have hd_lb : ((ℓ - 1 : ℕ) : ℕ∞) ≤ dRank (galUr 3 (↥Fbase)) :=
    GalUrGeneratorLowerBound (↥Fbase) hTR hGal hdeg ℓ hℓ2 M' hM'fin φ
  -- ===== Step 5.3: split primes (Prop36) =====
  obtain ⟨q, hqInj, hqPrimeNotT, hqRest⟩ :=
    Prop36ChebotarevApplication (↥Fbase) hfg ((ℓ - 1) ^ 2 / 100) ht_pos ∅
  have hqSplitF : ∀ b, SplitsCompletelyRat (q b) (↥Fbase) := fun b => (hqRest b).2.1
  -- Frobenius section σ over the (prime b, prime v | q b) index
  have hqRest2 : ∀ w : (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
        {v : Ideal (𝓞 (↥Fbase)) //
          v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 (↥Fbase))}),
      ∃ s : galUr 3 (↥Fbase),
        Workspace.Types.UnramifiedProPExtension.IsFrobeniusRepAt 3 (↥Fbase) s
            (w.2 : Ideal (𝓞 (↥Fbase))) ∧
          s ∈ frattiniOpen (galUr 3 (↥Fbase)) :=
    fun w => (hqRest w.1).2.2 (w.2 : Ideal (𝓞 (↥Fbase))) w.2.2
  choose σ hσfrob hσfrat using hqRest2
  -- N := closed normal closure of the killed Frobenius family
  set N := (Subgroup.normalClosure (Set.range σ)).topologicalClosure with hN_def
  haveI hNnorm : N.Normal := by
    rw [hN_def]
    exact Subgroup.is_normal_topologicalClosure (Subgroup.normalClosure (Set.range σ))
  have hNclosed : IsClosed (N : Set (galUr 3 (↥Fbase))) := by
    rw [hN_def]; exact Subgroup.isClosed_topologicalClosure _
  -- ===== Steps 6-7: infinite quotient (Group E) =====
  obtain ⟨hNontriv, hInf, hFGbar, hProPbar, hdbar, hrbar⟩ :=
    hE (↥Fbase) hTR hGal hdeg hno hpro hfg ℓ hL0E hd_lb q hqInj hqSplitF σ hσfrob hσfrat N hN_def
  -- ===== Step 8: descending chain (correspondence (b)) =====
  obtain ⟨_, _, _, hCorrB⟩ := UnramifiedProPTowerCorrespondence (↥Fbase)
  obtain ⟨Hchain, hHnorm, hHopen, hNH, hH0, hHanti, hHidxpos, hHidxtop⟩ :=
    hCorrB N hNnorm hNclosed hInf hFGbar hProPbar
  -- ===== Step 9: tower fields (Group F) =====
  obtain ⟨Fj, hFjeq, hFj0, hFjmono, hFjtop⟩ :=
    UnramifiedProPTowerFields (↥Fbase) N hNnorm hNclosed hInf hFGbar hProPbar
      Hchain hHnorm hHopen hNH hH0 hHanti hHidxpos hHidxtop
  -- Frobenius reps lie in N (needed for Group G)
  have hq_G : ∀ b, (q b).Prime ∧ q b % 4 = 1 ∧ SplitsCompletelyRat (q b) (↥Fbase) ∧
      ∀ v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 (↥Fbase)),
        ∃ s : galUr 3 (↥Fbase),
          Workspace.Types.UnramifiedProPExtension.IsFrobeniusRepAt 3 (↥Fbase) s v ∧ s ∈ N := by
    intro b
    refine ⟨(hqPrimeNotT b).1, (hqRest b).1, (hqRest b).2.1, ?_⟩
    intro v hv
    refine ⟨σ ⟨b, ⟨v, hv⟩⟩, hσfrob ⟨b, ⟨v, hv⟩⟩, ?_⟩
    rw [hN_def]
    exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨⟨b, ⟨v, hv⟩⟩, rfl⟩)
  -- ===== Step 10: per-layer package (Group G) =====
  have hlayer := TowerLayerProperties (↥Fbase) hTR hGal hdeg N Hchain hHopen hHnorm hNH Fj hFjeq
    ((ℓ - 1) ^ 2 / 100) q hq_G
  -- ===== Step 4: root-discriminant bound (Group D) via the Nat.nth bridge =====
  have hbridge : ∀ i : Fin ℓ, (r i : ℕ) = Nat.nth (fun n => n.Prime ∧ n % 3 = 1) (i : ℕ) := by
    intro i
    have hr_inj : Function.Injective r := hr_mono.injective
    have hri_inj : Function.Injective (fun a : Fin ℓ => (r a : ℕ)) :=
      fun a b h => hr_inj (PNat.coe_injective h)
    have hpi : (fun n => n.Prime ∧ n % 3 = 1) (r i : ℕ) := ⟨hp i, hm i⟩
    have hcount : Nat.count (fun n => n.Prime ∧ n % 3 = 1) (r i : ℕ) = (i : ℕ) := by
      rw [Nat.count_eq_card_filter_range]
      have hset : {x ∈ Finset.range (r i : ℕ) | (fun n => n.Prime ∧ n % 3 = 1) x}
          = (Finset.Iio i).image (fun a : Fin ℓ => (r a : ℕ)) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_Iio]
        constructor
        · rintro ⟨hylt, hyp, hym⟩
          by_contra hnex
          push_neg at hnex
          have hnoteq : ¬ ∃ k, (r k : ℕ) = y := by
            rintro ⟨k, hk⟩
            have hlt : (r k : ℕ) < (r i : ℕ) := by rw [hk]; exact hylt
            have hki : k < i := hr_mono.lt_iff_lt.mp ((PNat.coe_lt_coe _ _).mp hlt)
            exact hnex k hki hk
          have := hskip y hyp hym hnoteq i
          omega
        · rintro ⟨a, hai, hay⟩
          subst hay
          exact ⟨(PNat.coe_lt_coe _ _).mpr (hr_mono hai), hp a, hm a⟩
      rw [hset, Finset.card_image_of_injective _ hri_inj, Fin.card_Iio]
    calc (r i : ℕ)
        = Nat.nth (fun n => n.Prime ∧ n % 3 = 1)
            (Nat.count (fun n => n.Prime ∧ n % 3 = 1) (r i : ℕ)) := (Nat.nth_count hpi).symm
      _ = Nat.nth (fun n => n.Prime ∧ n % 3 = 1) (i : ℕ) := by rw [hcount]
  have hDeq : (D : ℕ) = ∏ i ∈ Finset.range ℓ, Nat.nth (fun n => n.Prime ∧ n % 3 = 1) i := by
    rw [hD_prod,
      ← Fin.prod_univ_eq_prod_range (fun k => Nat.nth (fun n => n.Prime ∧ n % 3 = 1) k) ℓ]
    exact Finset.prod_congr rfl (fun i _ => hbridge i)
  have hDF_prod : (NumberField.discr (↥Fbase)).natAbs
      = (∏ i ∈ Finset.range ℓ, Nat.nth (fun n => n.Prime ∧ n % 3 = 1) i) ^ 2 := by
    rw [hDF, hDeq]
  obtain ⟨_, hP1_rd⟩ := hD_body ℓ hℓ0D (↥Fbase) hTR hdeg hDF_prod
  -- ===== Step 11-12: P5 tail + P6 (Group I) =====
  obtain ⟨hIpos, hIlog, hIP6⟩ := hI_body ℓ hL0I (↥Fbase) hTR hdeg hP1_rd
  -- ===== Step 13: assemble =====
  refine ⟨↥Fbase, inferInstance, nfF, q, Fj,
    (2 * rootDiscriminant (↥Fbase)) ^ (2 * Cclass), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hTR, hGal, hdeg, hno, hP1_rd⟩
  · exact ⟨hFj0, hFjmono, hFjtop⟩
  · exact ⟨hqInj, fun b => (hqPrimeNotT b).1⟩
  · intro j
    obtain ⟨instFD, instNF, hGalj, hUnrj, hPGj, hTRj, hrdj, hsplitj⟩ := hlayer j
    haveI := instNF
    haveI : NumberField.IsTotallyReal (↥Fbase) := hTR
    haveI : NumberField.IsTotallyReal (↥(Fj j)) := hTRj
    obtain ⟨_, hKbound⟩ :=
      CMModelDiscriminantClassNumberBounds (↥Fbase) (↥(Fj j)) hrdj Cclass hCclass_pos hClass
        ((2 * rootDiscriminant (↥Fbase)) ^ (2 * Cclass)) rfl
    exact ⟨instFD, instNF, hGalj, hUnrj, hPGj, hTRj, hrdj, hsplitj, hKbound⟩
  · exact ⟨hIpos, hIlog⟩
  · exact hIP6
