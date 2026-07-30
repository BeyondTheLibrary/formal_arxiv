import Mathlib
import Workspace.Types.AdmissibleDatum
import Workspace.Types.CMAdjoinI
import Workspace.Types.SplittingRamification
import Workspace.ProofLemmas.ConjAutSwapPrimeOverQ
import Workspace.ProofLemmas.MultiplicityPrimeOverRationalPrime
import Workspace.ProofLemmas.MultiplicityTransportConjAut
import Workspace.ProofLemmas.PrimeOverQbLiesOverPrimeOverQ

open scoped NumberField
open Workspace.Types.AdmissibleDatum
open Workspace.Types.CMAdjoinI
open Workspace.Types.SplittingRamification

set_option maxHeartbeats 800000

open Classical in
/-- Enumerate a fixed-point-free involution on a finite set into representative pairs. -/
private theorem pairEnum {α : Type*} [LinearOrder α] (T : Finset α) (c : α → α)
    (hcT : ∀ a ∈ T, c a ∈ T) (hinv : ∀ a ∈ T, c (c a) = a) (hfree : ∀ a ∈ T, c a ≠ a) :
    ∃ (P Pc : Fin (T.card / 2) → α),
      (∀ s, P s ∈ T) ∧ (∀ s, c (P s) = Pc s) ∧ (∀ s, Pc s ≠ P s) ∧
      Function.Injective (Sum.elim P Pc) ∧
      (Finset.univ.image P ∪ Finset.univ.image Pc = T) := by
  set R := T.filter (fun a => a < c a) with hR
  set Q := T.filter (fun a => c a < a) with hQ
  have hcRQ : ∀ a ∈ R, c a ∈ Q := by
    intro a ha
    rw [hR, Finset.mem_filter] at ha
    rw [hQ, Finset.mem_filter]
    refine ⟨hcT a ha.1, ?_⟩
    rw [hinv a ha.1]; exact ha.2
  have hcQR : ∀ a ∈ Q, c a ∈ R := by
    intro a ha
    rw [hQ, Finset.mem_filter] at ha
    rw [hR, Finset.mem_filter]
    refine ⟨hcT a ha.1, ?_⟩
    rw [hinv a ha.1]; exact ha.2
  have hRQcard : R.card = Q.card := by
    apply Finset.card_bij' (fun a _ => c a) (fun a _ => c a) hcRQ hcQR
    · intro a ha; rw [hR, Finset.mem_filter] at ha; exact hinv a ha.1
    · intro a ha; rw [hQ, Finset.mem_filter] at ha; exact hinv a ha.1
  have hRQdisj : Disjoint R Q := by
    rw [Finset.disjoint_filter]
    intro a _ h; exact not_lt.mpr (le_of_lt h)
  have hRQunion : R ∪ Q = T := by
    rw [hR, hQ, ← Finset.filter_or]
    apply Finset.filter_true_of_mem
    intro a ha
    rcases lt_trichotomy a (c a) with h | h | h
    · exact Or.inl h
    · exact absurd h.symm (hfree a ha)
    · exact Or.inr h
  have hTcard : T.card = 2 * R.card := by
    rw [← hRQunion, Finset.card_union_of_disjoint hRQdisj, hRQcard]; ring
  have hRcard : R.card = T.card / 2 := by rw [hTcard]; omega
  let e := R.orderIsoOfFin hRcard
  have hmem : ∀ s : Fin (T.card / 2), (e s : α) ∈ T ∧ (e s : α) < c (e s : α) :=
    fun s => Finset.mem_filter.mp (e s).2
  refine ⟨fun s => (e s : α), fun s => c (e s : α), ?_, ?_, ?_, ?_, ?_⟩
  · intro s; exact (hmem s).1
  · intro s; rfl
  · intro s; exact (ne_of_lt (hmem s).2).symm
  · rintro (s | s) (t | t) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (e.injective (Subtype.ext h))
    · exfalso
      have h1 : (e s : α) ∈ R := (e s).2
      have h2 : c (e t : α) ∈ Q := hcRQ _ (e t).2
      rw [← h] at h2
      exact (Finset.disjoint_left.mp hRQdisj h1) h2
    · exfalso
      have h1 : (e t : α) ∈ R := (e t).2
      have h2 : c (e s : α) ∈ Q := hcRQ _ (e s).2
      rw [h] at h2
      exact (Finset.disjoint_left.mp hRQdisj h1) h2
    · have hi := congrArg c h
      rw [hinv _ (hmem s).1, hinv _ (hmem t).1] at hi
      exact congrArg Sum.inr (e.injective (Subtype.ext hi))
  · ext x
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨s, hs⟩ | ⟨s, hs⟩)
      · rw [← hs]; exact (hmem s).1
      · rw [← hs]; exact (Finset.mem_filter.mp (hcRQ _ (e s).2)).1
    · intro hxT
      rw [← hRQunion, Finset.mem_union] at hxT
      rcases hxT with hxR | hxQ
      · exact Or.inl ⟨e.symm ⟨x, hxR⟩, by rw [e.apply_symm_apply]⟩
      · refine Or.inr ⟨e.symm ⟨c x, hcQR x hxQ⟩, ?_⟩
        rw [e.apply_symm_apply]
        exact hinv x (Finset.mem_filter.mp hxQ).1

open Polynomial in
/-- `conjAut` induces an involution on ideals of `𝓞 K`. -/
private theorem conjIdealInvol (d : AdmissibleDatum) (I : Ideal (𝓞 d.K)) :
    Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin))
      (Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) I) = I := by
  set h := d.h_adjoin
  set iota := h.choose with hiota
  have hsqι : iota ^ 2 = -1 := h.choose_spec.1
  have hadjι : IntermediateField.adjoin d.L {iota} = ⊤ := h.choose_spec.2
  have hint : IsIntegral d.L iota := ⟨X ^ 2 + 1, by monicity!, by simp [hsqι]⟩
  have halg : IsAlgebraic d.L iota := hint.isAlgebraic
  have hcι2 : (conjAut h iota) ^ 2 = -1 := by rw [← map_pow, hsqι, map_neg, map_one]
  have hcases : conjAut h iota = iota ∨ conjAut h iota = -iota := by
    have hfac : (conjAut h iota - iota) * (conjAut h iota + iota) = 0 := by
      have hz : (conjAut h iota) ^ 2 - iota ^ 2 = 0 := by rw [hcι2, hsqι]; ring
      linear_combination hz
    rcases mul_eq_zero.mp hfac with hh | hh
    · left; exact sub_eq_zero.mp hh
    · right; linear_combination hh
  have hinvι : conjAut h (conjAut h iota) = iota := by
    rcases hcases with hh | hh
    · rw [hh, hh]
    · rw [hh, map_neg, hh, neg_neg]
  have hadjalg : Algebra.adjoin d.L {iota} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element halg hadjι
  have hinv : ∀ y : d.K, conjAut h (conjAut h y) = y := by
    have hEq : ((conjAut h).toAlgHom.comp (conjAut h).toAlgHom) = AlgHom.id d.L d.K := by
      apply AlgHom.ext_of_adjoin_eq_top hadjalg
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst hz
      simpa using hinvι
    intro y
    have := AlgHom.congr_fun hEq y
    simpa using this
  -- lift to 𝓞 K then to ideals
  have hnat : ∀ y : 𝓞 d.K, algebraMap (𝓞 d.K) d.K
      (NumberField.RingOfIntegers.mapAlgEquiv (conjAut h) y)
        = conjAut h (algebraMap (𝓞 d.K) d.K y) := by
    intro y
    simp [NumberField.RingOfIntegers.mapAlgEquiv, NumberField.RingOfIntegers.mapAlgHom]
  have hOinv : ∀ x : 𝓞 d.K,
      NumberField.RingOfIntegers.mapAlgEquiv (conjAut h)
        (NumberField.RingOfIntegers.mapAlgEquiv (conjAut h) x) = x := by
    intro x
    refine IsFractionRing.injective (𝓞 d.K) d.K ?_
    rw [hnat, hnat, hinv]
  show Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut h) : 𝓞 d.K →+* 𝓞 d.K)
      (Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut h) : 𝓞 d.K →+* 𝓞 d.K) I) = I
  rw [Ideal.map_map]
  have hcomp : ((NumberField.RingOfIntegers.mapAlgEquiv (conjAut h) : 𝓞 d.K →+* 𝓞 d.K).comp
      (NumberField.RingOfIntegers.mapAlgEquiv (conjAut h) : 𝓞 d.K →+* 𝓞 d.K)) = RingHom.id _ := by
    ext x; simpa using hOinv x
  rw [hcomp, Ideal.map_id]

/-- **Conjugate-pair indexing (Step 0 of Prop 2.2).** -/
theorem ConjugatePairIndexing (d : AdmissibleDatum)
    (hfact : (∀ b, SplitsCompletelyRat (d.q b) d.K) ∧
      (⋃ b, Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K)).ncard = 2 * d.t * deg d) :
    ∃ (P Pc : Fin (d.t * deg d) → IsDedekindDomain.HeightOneSpectrum (𝓞 d.K))
      (bidx : Fin (d.t * deg d) → Fin d.t)
      (S : Finset (Ideal (𝓞 d.K))),
      (∀ s, Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) (P s).asIdeal
              = (Pc s).asIdeal ∧ (Pc s).asIdeal ≠ (P s).asIdeal) ∧
      Function.Injective
        (Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal)) ∧
      (∀ s, (P s).asIdeal.LiesOver (Ideal.span {(d.q (bidx s) : ℤ)}) ∧
            (Pc s).asIdeal.LiesOver (Ideal.span {(d.q (bidx s) : ℤ)}) ∧
            (∀ b, multiplicity (P s).asIdeal
                (Ideal.span {(algebraMap ℤ (𝓞 d.K)) (d.q b)}) = if b = bidx s then 1 else 0) ∧
            (∀ b, multiplicity (Pc s).asIdeal
                (Ideal.span {(algebraMap ℤ (𝓞 d.K)) (d.q b)}) = if b = bidx s then 1 else 0)) ∧
      ((↑S : Set (Ideal (𝓞 d.K))) =
          ⋃ b, Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K)) ∧
      S.card = 2 * (d.t * deg d) ∧
      (S = (Finset.univ.image (fun s => (P s).asIdeal)) ∪
           (Finset.univ.image (fun s => (Pc s).asIdeal))) ∧
      (∀ (I : Ideal (𝓞 d.K)) (s : Fin (d.t * deg d)),
          multiplicity (P s).asIdeal
              (Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) I)
            = multiplicity (Pc s).asIdeal I ∧
          multiplicity (Pc s).asIdeal
              (Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) I)
            = multiplicity (P s).asIdeal I) := by
  classical
  obtain ⟨hsplit, hcardU⟩ := hfact
  set φ := NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin) with hφdef
  set c : Ideal (𝓞 d.K) → Ideal (𝓞 d.K) := fun I => Ideal.map φ I with hcdef
  -- maximality of (q_b)
  have hmax : ∀ b : Fin d.t, (Ideal.span {(d.q b : ℤ)}).IsMaximal := by
    intro b
    exact PrincipalIdealRing.isMaximal_of_irreducible
      (Nat.prime_iff_prime_int.mp (d.hq_prime b)).irreducible
  -- nonzero
  have hqne : ∀ b : Fin d.t, (Ideal.span {(d.q b : ℤ)}) ≠ ⊥ := by
    intro b hbot
    rw [Ideal.span_singleton_eq_bot] at hbot
    exact (d.hq_prime b).ne_zero (by exact_mod_cast hbot)
  -- finiteness of the union
  set U : Set (Ideal (𝓞 d.K)) :=
    ⋃ b, Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K) with hUdef
  have hUfin : U.Finite := by
    rw [hUdef]
    apply Set.finite_iUnion
    intro b
    haveI := hmax b
    exact primesOver_finite (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K)
  set T := hUfin.toFinset with hTdef
  -- membership characterization
  have hTmem : ∀ a : Ideal (𝓞 d.K), a ∈ T ↔
      ∃ b : Fin d.t, a ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K) := by
    intro a
    rw [hTdef, Set.Finite.mem_toFinset, hUdef, Set.mem_iUnion]
  -- T card
  have hTcard : T.card = 2 * (d.t * deg d) := by
    have h1 : T.card = U.ncard := by
      rw [hTdef, Set.ncard_eq_toFinset_card']
      congr 1
      exact (Set.Finite.toFinset_eq_toFinset hUfin).symm ▸ rfl
    rw [h1, hUdef, hcardU]; ring
  -- primality and nonzeroness of members
  have hTprime : ∀ a ∈ T, a.IsPrime := by
    intro a ha; exact ((hTmem a).mp ha).choose_spec.1
  have hTne : ∀ a ∈ T, a ≠ ⊥ := by
    intro a ha
    obtain ⟨b, hbp, hbo⟩ := (hTmem a).mp ha
    intro hbot
    subst hbot
    have : (Ideal.span {(d.q b : ℤ)}) = ⊥ := by
      rw [hbo.over, Ideal.under_bot]
    exact hqne b this
  -- LinearOrder for pairEnum
  letI : LinearOrder (Ideal (𝓞 d.K)) := linearOrderOfSTO WellOrderingRel
  -- involution / stability / freeness
  have hinvT : ∀ a ∈ T, c (c a) = a := by
    intro a _; rw [hcdef]; exact conjIdealInvol d a
  have hcTT : ∀ a ∈ T, c a ∈ T := by
    intro a ha
    obtain ⟨b, hbp, hbo⟩ := (hTmem a).mp ha
    haveI := hbp; haveI := hbo
    rw [hTmem]
    refine ⟨b, ?_, ?_⟩
    · rw [hcdef]; exact Ideal.map_isPrime_of_equiv φ
    · rw [hcdef]
      exact Ideal.map_equiv_liesOver a (Ideal.span {(d.q b : ℤ)}) (φ.restrictScalars ℤ)
  have hfreeT : ∀ a ∈ T, c a ≠ a := by
    intro a ha
    obtain ⟨b, hb⟩ := (hTmem a).mp ha
    obtain ⟨𝔮, h𝔮, h𝔓o⟩ := PrimeOverQbLiesOverPrimeOverQ d b a ⟨hb.1, hb.2⟩
    rw [hcdef]
    exact (ConjAutSwapPrimeOverQ d b 𝔮 h𝔮 a h𝔓o).2
  -- enumerate
  obtain ⟨P₀, Pc₀, hmem₀, hswap₀, hne₀, hinj₀, himg₀⟩ := pairEnum T c hcTT hinvT hfreeT
  have hdiv : T.card / 2 = d.t * deg d := by rw [hTcard]; omega
  let cs : Fin (d.t * deg d) ≃ Fin (T.card / 2) := finCongr hdiv.symm
  have hcsmem : ∀ s, P₀ (cs s) ∈ T := fun s => hmem₀ (cs s)
  -- bidx
  let bidx : Fin (d.t * deg d) → Fin d.t := fun s => ((hTmem (P₀ (cs s))).mp (hcsmem s)).choose
  have hbidx : ∀ s, P₀ (cs s) ∈
      Ideal.primesOver (Ideal.span {(d.q (bidx s) : ℤ)}) (𝓞 d.K) :=
    fun s => ((hTmem (P₀ (cs s))).mp (hcsmem s)).choose_spec
  -- Pc₀ membership
  have hPcmem : ∀ s, Pc₀ (cs s) ∈ T := by
    intro s; rw [← hswap₀ (cs s)]; exact hcTT _ (hcsmem s)
  -- wrap
  let P : Fin (d.t * deg d) → IsDedekindDomain.HeightOneSpectrum (𝓞 d.K) := fun s =>
    ⟨P₀ (cs s), (hbidx s).1, hTne _ (hcsmem s)⟩
  let Pc : Fin (d.t * deg d) → IsDedekindDomain.HeightOneSpectrum (𝓞 d.K) := fun s =>
    ⟨Pc₀ (cs s), hTprime _ (hPcmem s), hTne _ (hPcmem s)⟩
  set S : Finset (Ideal (𝓞 d.K)) :=
    (Finset.univ.image (fun s => (P s).asIdeal)) ∪
      (Finset.univ.image (fun s => (Pc s).asIdeal)) with hSdef
  refine ⟨P, Pc, bidx, S, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- property 1: swap
    intro s
    refine ⟨?_, ?_⟩
    · show Ideal.map φ (P₀ (cs s)) = Pc₀ (cs s)
      exact hswap₀ (cs s)
    · exact hne₀ (cs s)
  · -- property 2: injective
    have : (Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal))
        = (Sum.elim P₀ Pc₀) ∘ (Sum.map cs cs) := by
      ext (s | s) <;> rfl
    rw [this]
    exact hinj₀.comp (cs.injective.sumMap cs.injective)
  · -- property 3: ramification/multiplicity
    intro s
    have hPo : (P s).asIdeal.LiesOver (Ideal.span {(d.q (bidx s) : ℤ)}) := (hbidx s).2
    have hPco : (Pc s).asIdeal.LiesOver (Ideal.span {(d.q (bidx s) : ℤ)}) := by
      have : (Pc s).asIdeal = c ((P s).asIdeal) := (hswap₀ (cs s)).symm
      rw [this, hcdef]
      haveI := (hbidx s).1
      exact Ideal.map_equiv_liesOver (P₀ (cs s)) (Ideal.span {(d.q (bidx s) : ℤ)})
        (φ.restrictScalars ℤ)
    refine ⟨hPo, hPco, ?_, ?_⟩
    · intro b
      haveI := (P s).isPrime
      have hram_b : ∀ Q ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K),
          Ideal.ramificationIdx (Ideal.span {(d.q b : ℤ)}) Q = 1 :=
        fun Q hQ => ((hsplit b).2.2 Q hQ).1
      have hM := MultiplicityPrimeOverRationalPrime d (P s).asIdeal (P s).ne_bot b hram_b
      by_cases hb : b = bidx s
      · subst hb
        rw [if_pos rfl]; exact hM.1 hPo
      · rw [if_neg hb]
        apply hM.2
        intro hcon
        apply hb
        have heq : (Ideal.span {(d.q b : ℤ)}) = (Ideal.span {(d.q (bidx s) : ℤ)}) := by
          rw [hcon.over, hPo.over]
        have : (d.q b : ℤ) = (d.q (bidx s) : ℤ) := by
          rcases (Ideal.span_singleton_eq_span_singleton.mp heq) with hu
          rcases Int.associated_iff.mp hu with h | h
          · exact h
          · exfalso
            have := (d.hq_prime b).pos
            have := (d.hq_prime (bidx s)).pos
            omega
        exact d.hq_distinct (by exact_mod_cast this)
    · intro b
      haveI := (Pc s).isPrime
      have hram_b : ∀ Q ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K),
          Ideal.ramificationIdx (Ideal.span {(d.q b : ℤ)}) Q = 1 :=
        fun Q hQ => ((hsplit b).2.2 Q hQ).1
      have hM := MultiplicityPrimeOverRationalPrime d (Pc s).asIdeal (Pc s).ne_bot b hram_b
      by_cases hb : b = bidx s
      · subst hb
        rw [if_pos rfl]; exact hM.1 hPco
      · rw [if_neg hb]
        apply hM.2
        intro hcon
        apply hb
        have heq : (Ideal.span {(d.q b : ℤ)}) = (Ideal.span {(d.q (bidx s) : ℤ)}) := by
          rw [hcon.over, hPco.over]
        have : (d.q b : ℤ) = (d.q (bidx s) : ℤ) := by
          rcases Int.associated_iff.mp (Ideal.span_singleton_eq_span_singleton.mp heq) with h | h
          · exact h
          · exfalso
            have := (d.hq_prime b).pos
            have := (d.hq_prime (bidx s)).pos
            omega
        exact d.hq_distinct (by exact_mod_cast this)
  · -- property 4a: S as set = union
    have hST : S = T := by
      apply Finset.coe_injective
      have hcoeT : (↑T : Set (Ideal (𝓞 d.K))) = Set.range P₀ ∪ Set.range Pc₀ := by
        have hh := congrArg Finset.toSet himg₀
        simpa only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ]
          using hh.symm
      rw [hSdef, hcoeT]
      simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ]
      have hrP : Set.range (fun s => (P s).asIdeal) = Set.range P₀ := by
        ext y; constructor
        · rintro ⟨s, rfl⟩; exact ⟨cs s, rfl⟩
        · rintro ⟨s, rfl⟩; exact ⟨cs.symm s, by exact congrArg _ (cs.apply_symm_apply s)⟩
      have hrPc : Set.range (fun s => (Pc s).asIdeal) = Set.range Pc₀ := by
        ext y; constructor
        · rintro ⟨s, rfl⟩; exact ⟨cs s, rfl⟩
        · rintro ⟨s, rfl⟩; exact ⟨cs.symm s, by exact congrArg _ (cs.apply_symm_apply s)⟩
      rw [hrP, hrPc]
    rw [hST, hTdef, Set.Finite.coe_toFinset]
  · -- property 4b: S.card
    have hST : S = T := by
      apply Finset.coe_injective
      have hcoeT : (↑T : Set (Ideal (𝓞 d.K))) = Set.range P₀ ∪ Set.range Pc₀ := by
        have hh := congrArg Finset.toSet himg₀
        simpa only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ]
          using hh.symm
      rw [hSdef, hcoeT]
      simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ]
      have hrP : Set.range (fun s => (P s).asIdeal) = Set.range P₀ := by
        ext y; constructor
        · rintro ⟨s, rfl⟩; exact ⟨cs s, rfl⟩
        · rintro ⟨s, rfl⟩; exact ⟨cs.symm s, by exact congrArg _ (cs.apply_symm_apply s)⟩
      have hrPc : Set.range (fun s => (Pc s).asIdeal) = Set.range Pc₀ := by
        ext y; constructor
        · rintro ⟨s, rfl⟩; exact ⟨cs s, rfl⟩
        · rintro ⟨s, rfl⟩; exact ⟨cs.symm s, by exact congrArg _ (cs.apply_symm_apply s)⟩
      rw [hrP, hrPc]
    rw [hST]; exact hTcard
  · -- property 6: S = image ∪ image
    rfl
  · -- property 5: valuation transport
    intro I s
    constructor
    · have hmap : Ideal.map φ (Pc s).asIdeal = (P s).asIdeal := by
        show Ideal.map φ (Pc₀ (cs s)) = P₀ (cs s)
        rw [← hswap₀ (cs s)]; exact conjIdealInvol d (P₀ (cs s))
      have := MultiplicityTransportConjAut φ (Pc s).asIdeal I
      rw [hmap] at this
      exact this
    · have hmap : Ideal.map φ (P s).asIdeal = (Pc s).asIdeal := hswap₀ (cs s)
      have := MultiplicityTransportConjAut φ (P s).asIdeal I
      rw [hmap] at this
      exact this
