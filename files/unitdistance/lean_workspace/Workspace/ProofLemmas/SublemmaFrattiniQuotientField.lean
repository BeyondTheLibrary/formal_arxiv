import Mathlib
import Workspace.Types.UnramifiedProPExtension
import Workspace.Types.ProPGroup
import Workspace.ProofLemmas.ProPBurnsideBasis
import Workspace.ProofLemmas.SublemmaKrullLayerFinite3Group
import Workspace.ProofLemmas.SublemmaFixedFieldKernel

open scoped NumberField
open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.ProPGroup

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

/-- **The Frattini quotient extension `E/F`.** -/
theorem SublemmaFrattiniQuotientField
    (F : Type) [Field F] [NumberField F]
    (hpro : IsProP 3 (galUr 3 F))
    (hfg : TopFinitelyGenerated (galUr 3 F)) :
    IsOpen (frattiniOpen (galUr 3 F) : Set (galUr 3 F)) ∧
      (frattiniOpen (galUr 3 F)).Normal ∧
      (∃ k : ℕ, (frattiniOpen (galUr 3 F)).index = 3 ^ k) ∧
      FiniteDimensional F (fixedFieldOf 3 F (frattiniOpen (galUr 3 F))) ∧
      ∃ _hgal : IsGalois F (fixedFieldOf 3 F (frattiniOpen (galUr 3 F))),
        (AlgEquiv.restrictNormalHom
            (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)))).ker
          = frattiniOpen (galUr 3 F) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  -- Burnside basis for the pro-3 group G = galUr 3 F
  obtain ⟨hcomm, hpow, d, hdrank, hcard⟩ := ProPBurnsideBasis 3 (galUr 3 F) hpro hfg
  -- normality of Φ from commutator containment
  have hnormal : (frattiniOpen (galUr 3 F)).Normal := by
    constructor
    intro n hn g
    have hc := hcomm g n
    have hrw : g * n * g⁻¹ = (g * n * g⁻¹ * n⁻¹) * n := by group
    rw [hrw]; exact Subgroup.mul_mem _ hc hn
  -- Φ is closed (intersection of closed maximal-open subgroups)
  have hclosed : IsClosed (frattiniOpen (galUr 3 F) : Set (galUr 3 F)) := by
    have h : (frattiniOpen (galUr 3 F) : Set (galUr 3 F))
        = ⋂ s ∈ {H : Subgroup (galUr 3 F) | IsMaximalOpenSubgroup H}, (s : Set (galUr 3 F)) := by
      rw [frattiniOpen, Subgroup.coe_sInf]
    rw [h]
    exact isClosed_biInter (fun s hs => Subgroup.isClosed_of_isOpen s hs.1)
  -- Φ has finite index 3^d, hence FiniteIndex
  haveI hfinq : Finite (galUr 3 F ⧸ frattiniOpen (galUr 3 F)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  haveI hfi : (frattiniOpen (galUr 3 F)).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  -- closed + finite index ⇒ open
  have hopen : IsOpen (frattiniOpen (galUr 3 F) : Set (galUr 3 F)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ hclosed
  -- index = 3^d
  have hindex : ∃ k : ℕ, (frattiniOpen (galUr 3 F)).index = 3 ^ k := ⟨d, hcard⟩
  -- FiniteDimensional + IsGalois of E = fixedFieldOf 3 F Φ (Krull correspondence)
  obtain ⟨hfd, hgal, hn, _hsurj, _hker, _hpg⟩ :=
    SublemmaKrullLayerFinite3Group F hpro (frattiniOpen (galUr 3 F)) hopen hnormal
  refine ⟨hopen, hnormal, hindex, hfd, hgal, ?_⟩
  -- kernel identity via the fixed-field kernel sublemma
  haveI : Normal F (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)) : Type _) := hn
  exact SublemmaFixedFieldKernel F (frattiniOpen (galUr 3 F)) hopen hnormal
