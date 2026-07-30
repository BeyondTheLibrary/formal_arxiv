import Mathlib
import Workspace.Types.SplittingRamification
import Workspace.Types.FrobeniusSplitting

open scoped NumberField Pointwise
open Workspace.Types.SplittingRamification Workspace.Types.FrobeniusSplitting

set_option maxHeartbeats 800000

theorem SublemmaSplitCompletelyFrobTrivial
    (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [FiniteDimensional F E]
    (v : Ideal (𝓞 F)) (hv : v ≠ ⊥) (hvp : v.IsPrime)
    (hsplit : SplitsCompletely (F := F) (M := E) v)
    (φ : E ≃ₐ[F] E) (hφ : IsFrobeniusAt φ v) :
    φ = 1 := by
  classical
  obtain ⟨P, hP_prime, hP_lies, hFrobP⟩ := hφ
  haveI : P.IsPrime := hP_prime
  haveI : P.LiesOver v := hP_lies
  have hPmem : P ∈ v.primesOver (𝓞 E) := ⟨hP_prime, hP_lies⟩
  let Psub : ↑(v.primesOver (𝓞 E)) := ⟨P, hPmem⟩
  -- Linchpin: the Galois action on `𝓞 E` is `galRestrict`.
  have hlinch : ∀ (σ : E ≃ₐ[F] E) (x : 𝓞 E),
      σ • x = galRestrict (𝓞 F) F E (𝓞 E) σ x := by
    intro σ x
    have hcompat : (algebraMap (𝓞 E) E) (σ • x) = σ ((algebraMap (𝓞 E) E) x) := rfl
    apply IsFractionRing.injective (𝓞 E) E
    rw [hcompat, algebraMap_galRestrict_apply]
  -- Hence the pointwise action on ideals is `Ideal.map (galRestrict σ)`.
  have hraw : ∀ (σ : E ≃ₐ[F] E) (I : Ideal (𝓞 E)),
      σ • I = Ideal.map (galRestrict (𝓞 F) F E (𝓞 E) σ) I := by
    intro σ I
    rw [Ideal.pointwise_smul_def]
    congr 1
    exact RingHom.ext (fun x => by rw [MulSemiringAction.toRingHom_apply]; exact hlinch σ x)
  -- Transport pretransitivity from the generic action to the AlgEquiv action on primesOver.
  haveI hpre : MulAction.IsPretransitive (E ≃ₐ[F] E) ↑(v.primesOver (𝓞 E)) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨σ, hσ⟩ :=
      (Ideal.isPretransitive_of_isGaloisGroup (B := 𝓞 E) v (E ≃ₐ[F] E)).exists_smul_eq a b
    refine ⟨σ, ?_⟩
    apply Subtype.ext
    rw [Ideal.coe_smul_primesOver_eq_map_galRestrict F E σ a]
    rw [Subtype.ext_iff, Ideal.coe_smul_primesOver σ a, hraw σ ↑a] at hσ
    exact hσ
  -- φ fixes P, hence φ ∈ stabilizer Psub
  have hmap : Ideal.map (galRestrict (𝓞 F) F E (𝓞 E) φ) P = P := by
    have hc := hFrobP.comap_eq
    calc Ideal.map (galRestrict (𝓞 F) F E (𝓞 E) φ) P
        = Ideal.map (galRestrict (𝓞 F) F E (𝓞 E) φ)
            (Ideal.comap (galRestrict (𝓞 F) F E (𝓞 E) φ).toAlgHom P) := by rw [hc]
      _ = P := Ideal.map_comap_of_surjective _
            (galRestrict (𝓞 F) F E (𝓞 E) φ).surjective P
  have hφstab : φ ∈ MulAction.stabilizer (E ≃ₐ[F] E) Psub := by
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    rw [Ideal.coe_smul_primesOver_eq_map_galRestrict F E φ Psub]
    exact hmap
  -- orbit-stabilizer forces the stabilizer to be trivial
  have hcardprimes : Nat.card ↑(v.primesOver (𝓞 E)) = Module.finrank F E := by
    rw [Nat.card_coe_set_eq]; exact hsplit.1
  have hcardG : Nat.card (E ≃ₐ[F] E) = Module.finrank F E := IsGalois.card_aut_eq_finrank F E
  have hindex : (MulAction.stabilizer (E ≃ₐ[F] E) Psub).index = Module.finrank F E := by
    rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ, hcardprimes]
  have hidxcard := Subgroup.index_mul_card (MulAction.stabilizer (E ≃ₐ[F] E) Psub)
  rw [hindex, hcardG] at hidxcard
  have hfr_pos : 0 < Module.finrank F E := Module.finrank_pos
  have hstab1 : Nat.card ↥(MulAction.stabilizer (E ≃ₐ[F] E) Psub) = 1 :=
    Nat.eq_of_mul_eq_mul_left hfr_pos (by rw [mul_one]; exact hidxcard)
  haveI : Subsingleton ↥(MulAction.stabilizer (E ≃ₐ[F] E) Psub) :=
    (Nat.card_eq_one_iff_unique.mp hstab1).1
  have h1mem : (1 : E ≃ₐ[F] E) ∈ MulAction.stabilizer (E ≃ₐ[F] E) Psub :=
    (MulAction.stabilizer (E ≃ₐ[F] E) Psub).one_mem
  have := Subsingleton.elim (⟨φ, hφstab⟩ : ↥(MulAction.stabilizer (E ≃ₐ[F] E) Psub)) ⟨1, h1mem⟩
  exact Subtype.ext_iff.mp this
