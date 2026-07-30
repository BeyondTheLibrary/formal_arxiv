import Mathlib
import Workspace.Types.SplittingRamification
import Workspace.Types.DiscriminantsClassNumber
import Workspace.Types.FrobeniusSplitting
import Workspace.Types.ProPGroup
import Workspace.Types.UnramifiedProPExtension
import Workspace.ProofLemmas.GalUrIsProP
import Workspace.ProofLemmas.SublemmaLayerIso
import Workspace.ProofLemmas.SublemmaKrullLayerFinite3Group
import Workspace.ProofLemmas.SublemmaFixedFieldKernel
import Workspace.ProofLemmas.SublemmaTotallyRealDescends
import Workspace.ProofLemmas.SublemmaRdPreserved
import Workspace.ProofLemmas.SublemmaSubextUnramified
import Workspace.ProofLemmas.SublemmaTrivialFrobSplits
import Workspace.ProofLemmas.SublemmaSplittingTransitive
import Workspace.ProofLemmas.GalUrOpenNormalThreePowerIndex

open scoped NumberField
open Workspace.Types.SplittingRamification
open Workspace.Types.DiscriminantsClassNumber
open Workspace.Types.ProPGroup
open Workspace.Types.UnramifiedProPExtension

set_option maxHeartbeats 1000000

theorem TowerLayerProperties
    (F : Type) [Field F] [NumberField F]
    (hTR : NumberField.IsTotallyReal F)
    (hGal : IsGalois ℚ F)
    (hdeg : Module.finrank ℚ F = 3)
    (N : Subgroup (galUr 3 F)) [N.Normal]
    (H : ℕ → Subgroup (galUr 3 F))
    (hHopen : ∀ j, IsOpen (H j : Set (galUr 3 F)))
    (hHnormal : ∀ j, (H j).Normal)
    (hNH : ∀ j, N ≤ H j)
    (Fj : ℕ → IntermediateField F (AlgebraicClosure F))
    (hFj : ∀ j, Fj j =
      IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
        (fixedFieldOf 3 F (H j)))
    (t : ℕ) (q : Fin t → ℕ)
    (hq : ∀ b, (q b).Prime ∧ q b % 4 = 1 ∧ SplitsCompletelyRat (q b) F ∧
      ∀ v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F),
        ∃ σ : galUr 3 F,
          Workspace.Types.UnramifiedProPExtension.IsFrobeniusRepAt 3 F σ v ∧ σ ∈ N) :
    ∀ j, ∃ (_ : FiniteDimensional F ↥(Fj j)) (_ : NumberField ↥(Fj j)),
      IsGalois F ↥(Fj j) ∧
      EverywhereUnramified F ↥(Fj j) ∧
      IsPGroup 3 (↥(Fj j) ≃ₐ[F] ↥(Fj j)) ∧
      NumberField.IsTotallyReal ↥(Fj j) ∧
      rootDiscriminant ↥(Fj j) = rootDiscriminant F ∧
      (∀ b, q b % 4 = 1 ∧ SplitsCompletelyRat (q b) ↥(Fj j)) := by
  intro j
  haveI := hTR
  -- Step 1: `G = galUr 3 F` is pro-3.
  have hpro : IsProP 3 (galUr 3 F) := GalUrIsProP F
  -- Step 2a: Krull correspondence package for the finite layer `E = fixedFieldOf 3 F (H j)`.
  obtain ⟨hfd, hgal, hn, hsurj, hker, hpg⟩ :=
    SublemmaKrullLayerFinite3Group F hpro (H j) (hHopen j) (hHnormal j)
  haveI := hfd
  haveI := hgal
  haveI := hn
  letI nfE : NumberField (fixedFieldOf 3 F (H j) : Type _) :=
    NumberField.of_module_finite F (fixedFieldOf 3 F (H j) : Type _)
  -- Step 2b: everywhere unramified for `E`.
  have hEU : EverywhereUnramified F (fixedFieldOf 3 F (H j) : Type _) :=
    SublemmaSubextUnramified F (fixedFieldOf 3 F (H j))
  -- Odd degree of `E/F` from the 3-group Galois group.
  have hodd : Odd (Module.finrank F (fixedFieldOf 3 F (H j) : Type _)) := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨n, hcard⟩ := hpg.exists_card_eq
    rw [← IsGalois.card_aut_eq_finrank F (fixedFieldOf 3 F (H j) : Type _), hcard]
    exact Odd.pow (by norm_num)
  -- Step 4a: total reality descends to `E`.
  have hTRE : NumberField.IsTotallyReal (fixedFieldOf 3 F (H j) : Type _) :=
    SublemmaTotallyRealDescends F (fixedFieldOf 3 F (H j) : Type _) hodd
  -- Step 4b: root discriminant preserved.
  have hRD : rootDiscriminant (fixedFieldOf 3 F (H j) : Type _) = rootDiscriminant F :=
    SublemmaRdPreserved F (fixedFieldOf 3 F (H j) : Type _) hEU.1
  -- Step 3: each `q b` splits completely in `E`.
  have hsplitE : ∀ b, q b % 4 = 1 ∧
      SplitsCompletelyRat (q b) (fixedFieldOf 3 F (H j) : Type _) := by
    intro b
    obtain ⟨hprime, hmod, hsplitF, hfrob⟩ := hq b
    refine ⟨hmod, ?_⟩
    have hqZ : (q b : ℤ) ≠ 0 := by exact_mod_cast hprime.ne_zero
    have hspan_ne : Ideal.span {(q b : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact hqZ
    -- complete splitting of each prime of `𝓞 F` above `q b` in `E/F`
    have hSC : ∀ v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F),
        SplitsCompletely (F := F) (M := (fixedFieldOf 3 F (H j) : Type _)) v := by
      intro v hv
      obtain ⟨σ, hσfrob, hσN⟩ := hfrob v hv
      -- v ≠ ⊥
      have hv_ne : v ≠ ⊥ := by
        rintro rfl
        have hover := hv.2.over
        rw [Ideal.under_bot ℤ (𝓞 F)] at hover
        exact hspan_ne hover
      -- Frobenius representative restricts to a Frobenius on the finite layer `E`.
      have hfrobE : Workspace.Types.FrobeniusSplitting.IsFrobeniusAt
          (AlgEquiv.restrictNormalHom (fixedFieldOf 3 F (H j) : Type _) σ) v :=
        hσfrob (fixedFieldOf 3 F (H j))
      -- σ ∈ N ≤ H j, so its restriction is trivial in Gal(E/F).
      have hmemH : σ ∈ H j := hNH j hσN
      have hσE1 : AlgEquiv.restrictNormalHom (fixedFieldOf 3 F (H j) : Type _) σ = 1 := by
        have hk := SublemmaFixedFieldKernel F (H j) (hHopen j) (hHnormal j)
        have hmem : σ ∈ MonoidHom.ker
            (AlgEquiv.restrictNormalHom (fixedFieldOf 3 F (H j) : Type _)) := by
          rw [hk]; exact hmemH
        simpa [MonoidHom.mem_ker] using hmem
      exact SublemmaTrivialFrobSplits F (fixedFieldOf 3 F (H j) : Type _) v hv_ne hv.1 hEU.1
        ⟨AlgEquiv.restrictNormalHom (fixedFieldOf 3 F (H j) : Type _) σ, hfrobE, hσE1⟩
    -- assemble complete splitting of the rational prime `q b` in `E` via the tower.
    exact (SublemmaSplittingTransitive F (fixedFieldOf 3 F (H j) : Type _) (q b)).mpr
      ⟨hsplitF, hSC⟩
  -- Step 0/5: transport the whole package from `E` to `Fj j` and assemble.
  obtain ⟨_e, hfdFj, hiffFD, hiffNF, hiffGal, hiffEU, himpPG, hiffTR, heqRD, hiffSC⟩ :=
    SublemmaLayerIso F (H j)
  rw [hFj j]
  haveI := hfdFj
  refine ⟨hfdFj, NumberField.of_module_finite F _, hiffGal.mp hgal, hiffEU.mp hEU,
    himpPG hpg, hiffTR.mp hTRE, heqRD.trans hRD, ?_⟩
  intro b
  exact ⟨(hsplitE b).1, (hiffSC (q b)).mp (hsplitE b).2⟩
