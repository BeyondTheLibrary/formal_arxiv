import Mathlib
import Workspace.Types.SplittingRamification

open scoped NumberField

open Workspace.Types.SplittingRamification

set_option maxHeartbeats 1000000

namespace SublemmaUnramifiedTransportAux

variable {R S S₁ : Type*} [CommRing R] [CommRing S] [CommRing S₁] [Algebra R S] [Algebra R S₁]

/-- `Ideal.map φ` composed with `Ideal.map φ.symm` is the identity. -/
lemma map_symm_map (φ : S ≃ₐ[R] S₁) (Q : Ideal S₁) :
    Ideal.map φ (Ideal.map φ.symm Q) = Q := by
  show Ideal.map (φ : S →+* S₁) (Ideal.map (φ.symm : S₁ →+* S) Q) = Q
  rw [Ideal.map_map]
  have h : ((φ : S →+* S₁).comp (φ.symm : S₁ →+* S)) = RingHom.id S₁ := by ext x; simp
  rw [h, Ideal.map_id]

/-- The set of primes over `p` in `S₁` is the image under `Ideal.map φ` of those in `S`. -/
lemma primesOver_image (φ : S ≃ₐ[R] S₁) (p : Ideal R) :
    p.primesOver S₁ = Ideal.map φ '' p.primesOver S := by
  ext Q
  simp only [Ideal.primesOver, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hQp, hQl⟩
    refine ⟨Ideal.map φ.symm Q, ⟨?_, ?_⟩, map_symm_map φ Q⟩
    · haveI := hQp; exact Ideal.map_isPrime_of_equiv φ.symm
    · haveI := hQl; exact Ideal.map_equiv_liesOver Q p φ.symm
  · rintro ⟨P, ⟨hPp, hPl⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · haveI := hPp; exact Ideal.map_isPrime_of_equiv φ
    · haveI := hPl; exact Ideal.map_equiv_liesOver P p φ

/-- Ramification index over `p` being `1` transfers along an algebra equivalence. -/
lemma ram_transfer (φ : S ≃ₐ[R] S₁) (p : Ideal R)
    (h : ∀ P ∈ p.primesOver S, p.ramificationIdx P = 1) :
    ∀ Q ∈ p.primesOver S₁, p.ramificationIdx Q = 1 := by
  intro Q hQ
  rw [primesOver_image φ p] at hQ
  obtain ⟨P, hPmem, rfl⟩ := hQ
  rw [Ideal.ramificationIdx_map_eq p P φ]
  exact h P hPmem

/-- Unramifiedness at infinite places transfers along an algebra equivalence over `F`. -/
lemma inf_transfer {F E Fj : Type*} [Field F] [Field E] [Field Fj]
    [Algebra F E] [Algebra F Fj] (e : E ≃ₐ[F] Fj)
    (hE : IsUnramifiedAtInfinitePlaces F E) : IsUnramifiedAtInfinitePlaces F Fj := by
  refine ⟨fun u => ?_⟩
  have hv := hE.isUnramified (u.comap (e : E →+* Fj))
  have h2 := hv.comap_algHom (e.symm : Fj →ₐ[F] E)
  have hcomp : (u.comap (e : E →+* Fj)).comap ((e.symm : Fj →ₐ[F] E) : Fj →+* E) = u := by
    rw [← NumberField.InfinitePlace.comap_comp]
    convert NumberField.InfinitePlace.comap_id u using 2
    ext x; simp
  rwa [hcomp] at h2

end SublemmaUnramifiedTransportAux

theorem SublemmaUnramifiedTransport
    {F : Type*} [Field F] [NumberField F]
    {A B : Type*} [Field A] [Field B] [NumberField A] [NumberField B]
    [Algebra F A] [Algebra F B]
    [IsScalarTower ℚ F A] [IsScalarTower ℚ F B]
    (g : A ≃ₐ[F] B) :
    EverywhereUnramified F A ↔ EverywhereUnramified F B := by
  set φ : 𝓞 A ≃ₐ[𝓞 F] 𝓞 B := NumberField.RingOfIntegers.mapAlgEquiv g with hφ
  constructor
  · rintro ⟨hfin, hinf⟩
    refine ⟨?_, ?_⟩
    · intro p hp hpp Q hQ
      exact SublemmaUnramifiedTransportAux.ram_transfer φ p (hfin p hp hpp) Q hQ
    · exact SublemmaUnramifiedTransportAux.inf_transfer g hinf
  · rintro ⟨hfin, hinf⟩
    refine ⟨?_, ?_⟩
    · intro p hp hpp P hP
      exact SublemmaUnramifiedTransportAux.ram_transfer φ.symm p (hfin p hp hpp) P hP
    · exact SublemmaUnramifiedTransportAux.inf_transfer g.symm hinf
